mod frame;

extern crate byteorder;
use byteorder::{LittleEndian, ReadBytesExt};

extern crate protobuf;
use protobuf::{parse_from_bytes}; //, ProtobufResult};
use protobuf::error::ProtobufError;

extern crate capstone;
use capstone::prelude::*;

extern crate memmap;
use memmap::MmapOptions;

use std::io::Cursor;
//use std::error::Error;
use std::fs::File;
//use std::io::{self, stderr};
use std::path::Path;
use std::{env, mem};
use std::collections::HashMap;

/*
macro_rules! fatal {
    ($($tt:tt)*) => {{
        use std::io::Write;
        writeln!(&mut ::std::io::stderr(), $($tt)*).unwrap();
        ::std::process::exit(1)
    }}
}
*/

/**
 * A container for trace frames.  We do not use protobuffers because
 * protobuffers can not stream output (the whole trace would have to
 * be in memory before being written) or input (the whole trace would
 * need to be unserialized to get one frame).
 *
 * The trace format is extremely simple. All numbers are
 * little-endian.
 *
 * [<uint64_t magic number>
 *  <uint64_t trace version number>
 *  <uint64_t bfd_architecture>
 *  <uint64_t bfd_machine, 0 for unspecified>
 *  <uint64_t n = number of trace frames>
 *  <uint64_t offset of field m (below)>
 *  [ <uint64_t sizeof(trace frame 0)>
 *    <trace frame 0>
 *    ..............
 *    <uint64_t sizeof(trace frame n)>
 *    <trace frame n> ]
 *  <uint64_t m, where a table of contents entry is given
 *  for m, 2m, 3m, ..., ceil(n/m)>
 *  [ <uint64_t offset of sizeof(trace frame m)>
 *    <uint64_t offset of sizeof(trace frame 2m)>
 *    ...
 *    <uint64_t offset of sizeof(trace frame ceil(n/m))> ]]
 *
 *  One additional feature that might be nice is log_2(n) lookup
 *  time using a hierarchical toc.
 */


const MAGIC_NUMBER: u64 = 7456879624156307493;
//const DEFAULT_FRAMES_PER_TOC_ENTRY:u64 = 10000;

const BFD_MACH_I386_I386 :u64 = 1;
const BFD_MACH_X86_64 :u64    = 64; // 64
const BFD_ARCH_I386:u64 = 9;
//const DEFAULT_ARCH:u64 = BFD_ARCH_I386;
//const DEFAULT_MACHINE:u64 = BFD_MACH_X86_64;

const OUT_TRACE_VERSION :u64 = 1;
const LOWEST_SUPPORTED_VERSION:u64 = 1;
const HIGHEST_SUPPORTED_VERSION:u64 = OUT_TRACE_VERSION;

#[repr(C)]
struct MoflowTraceHeader {
    magic_number:u64,
    trace_version:u64,
    bfd_arch:u64,
    bfd_machine:u64,
    num_trace_frames:u64,
    toc_offset:u64
}
const TRACE_HEADER_SIZE:usize = mem::size_of::<MoflowTraceHeader>();
const FIRST_FRAME_OFFSET:usize = TRACE_HEADER_SIZE;

struct LoadedModule {
    base_addr: u64,
    high_addr: u64,
    path: String,
}

struct TaintInfo {
    taint_predecessors: Vec<u64>,
}

struct MoflowTrace {
    //file: File,
    mmap: memmap::Mmap,
    header: MoflowTraceHeader,
    toc: Vec<usize>,
    frame_to_offset: Vec<usize>, // list of offsets for all frames
    offset_to_frame: HashMap<usize, u64>, // list of frames for all offsets
    loaded_modules: Vec<LoadedModule>, // list of offsets to load_module frames
    taint_info: Vec<TaintInfo>, // list of offsets to load_module frames
    taint_map: HashMap<String, u64>, // taint name -> parent id?
}

impl MoflowTrace {
    fn new(file_path: &str) -> Result<MoflowTrace, ProtobufError> {
        let file = File::open(&Path::new(file_path)).map_err(ProtobufError::IoError)?;
        let mmap = unsafe { MmapOptions::new().map(&file)? };  
        
        let slice = &mmap[0..TRACE_HEADER_SIZE];
        let header: MoflowTraceHeader = unsafe { std::ptr::read(slice.as_ptr() as *const _) };
        if header.magic_number != MAGIC_NUMBER { panic!("Bad Magic"); }

        let mut toc_offset = header.toc_offset as usize;
        let mut slice = &mmap[toc_offset..(toc_offset + 8)];
        toc_offset += 8;

        let frames_per_toc_entry = unsafe { std::ptr::read(slice.as_ptr() as *mut usize) };
        let toc_count = (header.num_trace_frames - 1) / frames_per_toc_entry as u64;
        let mut toc: Vec<usize> = Vec::new();
        
        for toc_table_index in 0 .. toc_count {
            slice = &mmap[toc_offset..(toc_offset + (8 * toc_table_index) as usize)];
            let toc_entry = unsafe { std::ptr::read(slice.as_ptr() as *mut usize) };
            toc.push(toc_entry);
        }

        let mut taint_info = Vec::with_capacity(header.num_trace_frames as usize);

        println!("");
        // create frame_index where index[frame_num] = trace_offset
        let mut loaded_modules = Vec::new();
        let mut frame_to_offset = Vec::new();
        let mut offset_to_frame = HashMap::new();
        let mut taint_map = HashMap::new();
        let mut mmap_offset = FIRST_FRAME_OFFSET;
        print!("\rIndexing trace... 0%");
        for frame_num in 0..(header.num_trace_frames) {
            if frame_num % 100 == 0 { print!("\rIndexing trace... {}%", (frame_num * 100/ header.num_trace_frames)); }
            frame_to_offset.push(mmap_offset);
            offset_to_frame.insert(mmap_offset, frame_num);
            let mut slice = &mmap[mmap_offset..(mmap_offset + 8)];
            let frame_size = unsafe { std::ptr::read(slice.as_ptr() as *mut usize) };
            mmap_offset += 8; // + frame_size; // update offset to point to frame data

            slice = &mmap[mmap_offset..(mmap_offset + frame_size)];
            let trace_frame :frame::frame = parse_from_bytes::<frame::frame>(slice).unwrap();
            mmap_offset += frame_size; // update offset to point to next frame size

            if trace_frame.has_modload_frame() == true { 
                let mf = trace_frame.get_modload_frame();
                let module = LoadedModule { base_addr: mf.get_low_address(), high_addr: mf.get_high_address(), path: mf.get_module_name().to_string() };
                loaded_modules.push(module);
            }
        }
        println!("\rIndexing trace... done.");
        
        Ok(MoflowTrace { 
            //file: file, 
            mmap: mmap,
            header: header,        
            toc: toc,
            frame_to_offset: frame_to_offset,
            offset_to_frame: offset_to_frame,
            loaded_modules: loaded_modules,
            taint_info: taint_info,
            taint_map: taint_map,
        })
    }

    fn pp_trace_header(&self)
    {
        println!("magic:   {:X}", self.header.magic_number);
        println!("version: {}", self.header.trace_version);
        let arch_str;
        match self.header.bfd_arch {
            BFD_ARCH_I386 => arch_str = "x86",
            _ => arch_str = "unknown",
        };
        let mach_str;
        match self.header.bfd_machine {
            BFD_MACH_I386_I386 => mach_str = "i386",
            BFD_MACH_X86_64 => mach_str = "X86_64",
            _ => mach_str = "unknown",
        };
        println!("arch:    {}", arch_str);
        println!("machine: {}",  mach_str);        
        //println!("toc offset:  {:?}", self.toc_offset);
        println!("frames:  {:?}", self.header.num_trace_frames);
    }

    fn pp_frame_range(&self, low: u64, high: u64)
    {
        for i in low .. high { self.pp_frame_num(i); }
    }
    fn pp_frame_num(&self, frame_num :u64)
    {
        let (frame, _) = self.extract_frame_by_num(frame_num);
        self.pp_frame(frame, frame_num);
    }
    fn pp_frame(&self, trace_frame: frame::frame, frame_num: u64)
    {   
        if trace_frame.has_modload_frame() {
            let modload_frame = trace_frame.get_modload_frame();
            println!("[{:5}] Loaded module: 0x{:016x} - 0x{:016x}  {}", frame_num, modload_frame.get_low_address(), modload_frame.get_high_address(), modload_frame.get_module_name());
            return;
        } 

        if trace_frame.has_taint_intro_frame() {
            let taint_intro_list = trace_frame.get_taint_intro_frame().get_taint_intro_list();
            let taint_list = taint_intro_list.get_elem();
            let first_byte = &taint_list[0];

            println!("");
            println!("[{:5}] Tainting {} bytes mapped at 0x{:016x} from source {} byte range {} - {}", 
                frame_num, 
                taint_list.len(), 
                first_byte.get_addr(), 
                first_byte.get_source_name(), 
                first_byte.get_offset(), 
                first_byte.get_offset() + taint_list.len() as u64);
            println!("");
            print!("     ");
            for taint_byte in taint_list {
                print!("{:X?} ", taint_byte.get_value());
                if taint_byte.get_taint_id() % 16 == 0 {
                    print!("\n     ");
                }
            }
            println!("");
            println!("");
            return;
        }

        if trace_frame.has_std_frame() {
            let std_frame = trace_frame.get_std_frame();
            self.pp_std_frame(std_frame, frame_num);

            return;
        }
        
        if trace_frame.has_key_frame() {
            println!("{:?}", trace_frame.get_key_frame());
            return;
        }
        
        if trace_frame.has_syscall_frame() {
            
            // the syscall numbers in the trace don't make sense, so skip for now
            /*
            let syscall = trace_frame.get_syscall_frame();
            let sysname_str = match syscall.get_number() {
                0 => "sys_read",
                1 => "sys_write",
                2 => "sys_open",
                3 => "sys_close",
                9 => "sys_mmap",
                _ => "sys_other",
            };
            println!("SYSCALL from thread {} at address 0x{:08X}: {}", 
                syscall.get_thread_id(),
                syscall.get_address(),
                sysname_str);            
            println!("{:?}", trace_frame.get_syscall_frame());
            */
            return;
        }
        
        if trace_frame.has_exception_frame() {
            let ex = trace_frame.get_exception_frame();
            if self.header.bfd_arch == 64 {
                println!("Exception code {} in thread {} at address 0x{:016X}",
                    ex.get_exception_number(),
                    ex.get_thread_id(),
                    ex.get_from_addr());
            } else {
                println!("Exception code {} in thread {} at address 0x{:08X}",
                    ex.get_exception_number(),
                    ex.get_thread_id(),
                    ex.get_from_addr());
            }
            return;
        }
        println!("XXXXXXXXXXXXXXXXX UNHANDLED FRAME XXXXXXXXXXXXXXXXXXXXX");
        println!("{:?}", trace_frame);
        println!("XXXXXXXXXXXXXXXXX UNHANDLED FRAME XXXXXXXXXXXXXXXXXXXXX");        
    }

    fn extract_frame_by_num(&self, frame_number: u64) -> (frame::frame, usize)
    {
        let mut mmap_offset = self.frame_to_offset[frame_number as usize] as usize;
        let mut slice = &self.mmap[mmap_offset..(mmap_offset + 8)];
        let frame_size = unsafe { std::ptr::read(slice.as_ptr() as *mut usize) };
        
        mmap_offset += 8; // update offset to point to frame data        
        slice = &self.mmap[mmap_offset..(mmap_offset + frame_size)];
        let trace_frame :frame::frame = parse_from_bytes::<frame::frame>(slice).unwrap();

        (trace_frame, frame_size)
    }

    fn pp_operand_info_op(&self, info: &frame::operand_info)
    {
        {
            // get string holding register or address name
            let mut op_str = "".to_string();
            let op_info_spec = info.get_operand_info_specific();        
            let z = op_info_spec.get_reg_operand();
            if op_info_spec.has_reg_operand() {
                let op = op_info_spec.get_reg_operand();
                op_str = format!("{}", op.get_name());
                match self.taint_map.get(&op.get_name().to_string()) {
                    None => {},
                    Some(v) => op_str = v.to_string(),
                }
            }
            else if op_info_spec.has_mem_operand() {
                let op = op_info_spec.get_mem_operand();
                op_str = format!("*0x{:<16X}", op.get_address());
            } else {
                println!("FIXME!!! {:?}", info.get_operand_info_specific());
            }

            // get string indicating read/write/index/base
            let mut op_use_str = "".to_string();
            let op_use = info.get_operand_usage();
            if op_use.get_read() == true { op_use_str = format!("{} read  ", op_use_str); } else { op_use_str = format!("{}       ", op_use_str); }
            if op_use.get_written() == true { op_use_str = format!("{} write ", op_use_str); } else { op_use_str = format!("{}       ", op_use_str); }
            if op_use.get_index() == true { op_use_str = format!("{} index  ", op_use_str); }
            if op_use.get_base() == true { op_use_str = format!("{} base  ", op_use_str); }

            //let mut op_use_str = "".to_string();
            let op_taint = info.get_taint_info();
            let mut taint_str = "".to_string();
            if op_taint.get_no_taint() == true { taint_str = format!("{} taint:none ", taint_str); }
            if op_taint.get_taint_id() != 0 { taint_str = format!("{} taint_id: {} ", taint_str, op_taint.get_taint_id()); }
            if op_taint.get_taint_multiple() == true { taint_str = format!("{} taint:multiple ", taint_str); }

            let v = match info.get_bit_length() {
                64 => Cursor::new(info.get_value()).read_u64::<LittleEndian>().unwrap() as u64,
                32 => Cursor::new(info.get_value()).read_u32::<LittleEndian>().unwrap() as u64,
                16 => Cursor::new(info.get_value()).read_u16::<LittleEndian>().unwrap() as u64,
                8 => Cursor::new(info.get_value()).read_u8().unwrap() as u64,
                _ => 0,
            };

            if op_taint.get_no_taint() == false && op_use.get_read() == true { taint_str = format!("{} TAINTED READ", taint_str)}
            println!("     {:20} = {:16X} {:2} bits {:15} {}", op_str, v, info.get_bit_length(), op_use_str, taint_str);

            //println!("{:?}", info.get_operand_usage());
            //println!("{:?}", info.get_taint_info());
        }
    }

    fn pp_operand_info(&self, op_info_list: &[frame::operand_info])
    {
        // display read operands first 
        for info in op_info_list {
            if info.get_operand_usage().get_read() == true {
                self.pp_operand_info_op(info);
            }
        }
        
        // display written operands second
        for info in op_info_list {
            // skip operands we displayed because they were read
            if info.get_operand_usage().get_written() == true && info.get_operand_usage().get_read() != true {                
                self.pp_operand_info_op(info);
            }
        }

        /*
        These are not present in the trace

        // display written operands second
        for info in op_info_list {
            if info.get_operand_usage().get_base() == true {
                pp_operand_info_op(info);
            }
        }
        // display written operands second
        for info in op_info_list {
            if info.get_operand_usage().get_index() == true {
                pp_operand_info_op(info);
            }
        }
        */

    }

    fn pp_std_frame(&self, std_frame: &frame::std_frame, frame_num: u64)
    {
        // this is probably expensive but making this global is hard 
        let mut cs = Capstone::new()
            .x86()
            .mode(arch::x86::ArchMode::Mode64)
            .syntax(arch::x86::ArchSyntax::Intel)
            .detail(false)
            .build()
            .expect("Failed to create Capstone object");

        let insns = cs.disasm_count(std_frame.get_rawbytes(), std_frame.get_address(), 1).expect("disas fail");
        for insn in insns.iter() {
            if self.header.bfd_arch == 64 {
            println!("[{:5}] tid={:<5} addr 0x{:016x}: {} {}", frame_num, std_frame.get_thread_id(), insn.address(), insn.mnemonic().unwrap(), insn.op_str().unwrap());
            } else {
                println!("# FRAME {:<6} ################################################################", frame_num);
                println!("");
                println!("     tid={:<5} addr 0x{:08x}: {} {}", std_frame.get_thread_id(), insn.address(), insn.mnemonic().unwrap(), insn.op_str().unwrap());
            }

        }
        self.pp_operand_info(std_frame.get_operand_pre_list().get_elem());
        println!("");
        
        //these don't exist
        //println!("operand values after:");
        //pp_operand_info(std_frame.get_operand_post_list().get_elem());
        
        //println!("---");
        
        //println!(" address: {}  thread: {} ", std_frame.get_address(), );
    }

}





fn main() {

    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("Usage: {} <moflow trace>", &args[0]);
        return
    }

    let trace = MoflowTrace::new(&args[1]).expect("\nError: failed to load trace\n");
    let header = &trace.header;
    println!("# TRACE HEADER ################################################################");
    trace.pp_trace_header();
    println!("##############################################################################");
    println!("");

    if header.trace_version > HIGHEST_SUPPORTED_VERSION || header.trace_version < LOWEST_SUPPORTED_VERSION {
        println!("Error: unsupported trace version");
        return
    }

    /*
    let _toc_len = trace.toc.len();
    
    for module in &trace.loaded_modules {
        //println!("module: {:016X} - {:016X}  {}", module.base_addr, module.high_addr, module.path);
    }
    */

    // print entire trace
    println!("# TRACE FRAMES ################################################################");
    trace.pp_frame_range(0, header.num_trace_frames);

    return
}

