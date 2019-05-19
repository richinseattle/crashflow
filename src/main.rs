//#![warn(clippy)]

mod frame;

extern crate byteorder;
use byteorder::{LittleEndian, ReadBytesExt};

extern crate protobuf;
use protobuf::error::ProtobufError;
use protobuf::parse_from_bytes; //, ProtobufResult};

extern crate capstone;
use capstone::prelude::*;

extern crate memmap;
use memmap::MmapOptions;

use std::io::Cursor;
//use std::error::Error;
use std::fs::File;
//use std::io::{self, stderr};
use std::collections::HashMap;
use std::path::Path;
use std::{env, mem, process};

use std::fmt; // impl Display for struct to_string

macro_rules! fatal {
    ($($tt:tt)*) => {{
        use std::io::Write;
        writeln!(&mut ::std::io::stderr(), $($tt)*).unwrap();
        ::std::process::exit(1)
    }}
}

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

const BFD_MACH_I386_I386: u64 = 1;
const BFD_MACH_X86_64: u64 = 64; // 64
const BFD_ARCH_I386: u64 = 9;
//const DEFAULT_ARCH: u64 = BFD_ARCH_I386;
//const DEFAULT_MACHINE: u64 = BFD_MACH_X86_64;

const OUT_TRACE_VERSION: u64 = 1;
const LOWEST_SUPPORTED_VERSION: u64 = 1;
const HIGHEST_SUPPORTED_VERSION: u64 = OUT_TRACE_VERSION;

#[repr(C)]
struct MoflowTraceHeader {
    magic_number: u64,
    trace_version: u64,
    bfd_arch: u64,
    bfd_machine: u64,
    num_trace_frames: u64,
    toc_offset: u64,
}

const TRACE_HEADER_SIZE: usize = mem::size_of::<MoflowTraceHeader>();
const FIRST_FRAME_OFFSET: usize = TRACE_HEADER_SIZE;

struct LoadedModule {
    frame_num: u64,
    base_addr: u64,
    high_addr: u64,
    filename: String,
}
impl LoadedModule {
    fn new(
        frame_num: u64,
        module_frame: &frame::modload_frame,
    ) -> Result<LoadedModule, ProtobufError> {
        return Ok(LoadedModule {
            frame_num: frame_num,
            base_addr: module_frame.get_low_address(),
            high_addr: module_frame.get_high_address(),
            filename: module_frame.get_module_name().to_string(),
        });
    }
}
impl fmt::Display for LoadedModule {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmt,
            "{:#016x} - {:#016x} {}",
            self.base_addr, self.high_addr, self.filename
        )
    }
}

struct ExceptionRecord {
    frame_num: u64,
    exception_code: u64,
    thread_id: u64,
    address: u64,
}
impl ExceptionRecord {
    fn new(
        frame_num: u64,
        exception_record: &frame::exception_frame,
    ) -> Result<ExceptionRecord, ProtobufError> {
        return Ok(ExceptionRecord {
            frame_num: frame_num,
            exception_code: exception_record.get_exception_number(),
            thread_id: exception_record.get_thread_id(),
            address: exception_record.get_from_addr(),
        });
    }
}
impl fmt::Display for ExceptionRecord {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmt,
            "Exception code {} in thread {} at address {:}",
            self.exception_code, self.thread_id, self.address
        )
    }
}

struct TaintIntro {
    frame_num: u64,
    address: u64,
    size: usize,
    source: String,
    source_offset: usize,
    taint_id: u32,
    data: Vec<u8>,
}
impl TaintIntro {
    fn new(frame_num: u64, frame: &frame::taint_intro_frame) -> Result<TaintIntro, ProtobufError> {
        let taint_list = frame.get_taint_intro_list().get_elem();
        let first_byte = &taint_list[0];

        let mut data = Vec::new();
        for taint_byte in taint_list {
            data.push(taint_byte.get_value()[0]);
        }

        return Ok(TaintIntro {
            frame_num: frame_num,
            address: first_byte.get_addr() as u64,
            size: taint_list.len() as usize,
            taint_id: first_byte.get_taint_id() as u32,
            source: first_byte.get_source_name().to_string(),
            source_offset: first_byte.get_offset() as usize,
            data: data,
        });
    }
}
impl fmt::Display for TaintIntro {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmt,
            "Tainting {} bytes mapped at {:#016x} from source {} byte range {} - {}",
            self.size,
            self.address,
            self.source,
            self.source_offset,
            self.source_offset + self.size
        )
    }
}

enum OperandAccess {
    Read,
    Write,
    ReadWrite,
}

struct Instruction {
    frame_num: u64,
    address: u64,
}

//struct Syscall {}

impl fmt::Display for Instruction {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let insn_string = "".to_string();
        write!(fmt, "{}", insn_string)
    }
}

struct TaintInfo {
    //taint_predecessors: Vec<u64>,
    taint_info: Vec<TaintInfo>, // list of offsets to load_module frames
    ssa_labels: HashMap<String, String>, // taint name -> parent id?
}
impl TaintInfo {
    fn new() -> TaintInfo {
        //let mut taint_predecessors: Vec::new();
        let mut taint_info: Vec<TaintInfo> = Vec::new(); // = Vec::with_capacity(header.num_trace_frames as usize);
        let mut ssa_labels = HashMap::new();

        TaintInfo {
            taint_info: taint_info,
            ssa_labels: ssa_labels,
        }
    }

    //fn set_ssa_label((&mut self, operand_name: &String) -> String {
    //}
    fn get_ssa_label(&mut self, operand_name: &String) -> String {
        match self.ssa_labels.get(operand_name) {
            None => {
                let ssa_label = format!("ssa_{}_0", operand_name);
                self.ssa_labels
                    .insert(operand_name.to_string(), ssa_label.to_string());
                ssa_label.to_string()
            }
            Some(v) => v.to_string(),
        }
    }
}

struct MoflowTrace {
    mmap: memmap::Mmap,
    header: MoflowTraceHeader,
    toc: Vec<u64>,
    frame_idx: Vec<(usize, u64)>, // (offset, len) list of offsets for all frames
    offset_to_frame: HashMap<usize, u64>, // list of frames for all offsets
    loaded_modules: Vec<LoadedModule>, // list of offsets to load_module frames
    taint_intros: Vec<TaintIntro>,
    exception_records: Vec<ExceptionRecord>,
    std_frame_idx: Vec<(usize, u64)>, // offset, len
}

impl MoflowTrace {
    // mmap file, parse header, and index offsets for various trace packets
    fn new(file_path: &str) -> Result<MoflowTrace, ProtobufError> {
        let file = File::open(&Path::new(file_path)).map_err(ProtobufError::IoError)?;
        let mmap = unsafe { MmapOptions::new().map(&file)? };

        // read trace header as raw struct from mmap
        let slice = &mmap[0..TRACE_HEADER_SIZE];
        let header: MoflowTraceHeader = unsafe { std::ptr::read(slice.as_ptr() as *const _) };

        if header.magic_number != MAGIC_NUMBER {
            panic!("Bad Magic");
        }

        if header.trace_version > HIGHEST_SUPPORTED_VERSION
            || header.trace_version < LOWEST_SUPPORTED_VERSION
        {
            panic!("Error: unsupported trace version");
        }

        let mut toc_offset = header.toc_offset as usize;
        let mut slice = &mmap[toc_offset..(toc_offset + 8)];
        toc_offset += 8;

        let frames_per_toc_entry = unsafe { std::ptr::read(slice.as_ptr() as *mut u64) };
        let toc_count = (header.num_trace_frames - 1) / frames_per_toc_entry; // as u64;
        let mut toc: Vec<u64> = Vec::with_capacity(toc_count as usize);

        for toc_table_index in 0..toc_count {
            slice = &mmap[toc_offset..(toc_offset + (8 * toc_table_index) as usize)];
            let toc_entry = unsafe { std::ptr::read(slice.as_ptr() as *mut u64) };
            toc.push(toc_entry);
        }

        println!("");
        // create frame_index where index[frame_num] = trace_offset
        // preallocate so parsing isnt interrupted (keep cache / TLB clean)
        let mut loaded_modules = Vec::with_capacity(32);
        let mut taint_intro_list = Vec::with_capacity(8);
        let mut exception_records = Vec::with_capacity(8);
        let mut frame_idx = Vec::with_capacity(header.num_trace_frames as usize);
        let mut std_frame_idx = Vec::with_capacity(header.num_trace_frames as usize);
        let mut offset_to_frame = HashMap::new();
        let mut mmap_offset = FIRST_FRAME_OFFSET;
        print!("\rIndexing trace... 0%");
        for frame_num in 0..(header.num_trace_frames) {
            // leet gfx
            if frame_num % 100 == 0 {
                print!(
                    "\rIndexing trace... {}%",
                    (frame_num * 100 / header.num_trace_frames)
                );
            }

            let mut slice = &mmap[mmap_offset..(mmap_offset + 8)];
            let frame_size = unsafe { std::ptr::read(slice.as_ptr() as *mut u64) };
            mmap_offset += 8; // update offset to point to frame data
            slice = &mmap[mmap_offset..(mmap_offset + frame_size as usize)];
            let trace_frame: frame::frame = parse_from_bytes::<frame::frame>(slice).unwrap();

            frame_idx.push((mmap_offset as usize, frame_size));
            offset_to_frame.insert(mmap_offset as usize, frame_num);

            if trace_frame.has_std_frame() == true {
                std_frame_idx.push((mmap_offset as usize, frame_num));
            }

            if trace_frame.has_modload_frame() == true {
                let modload_frame = trace_frame.get_modload_frame();
                let loaded_module = LoadedModule::new(frame_num, modload_frame)
                    .expect("Error parsing modload_frame");
                loaded_modules.push(loaded_module);
            }

            if trace_frame.has_taint_intro_frame() == true {
                let taint_intro_frame = trace_frame.get_taint_intro_frame();
                let taint_intro = TaintIntro::new(frame_num, taint_intro_frame)
                    .expect("Error parsing taint_intro_frame");;
                taint_intro_list.push(taint_intro);
            }

            if trace_frame.has_exception_frame() == true {
                let exception_frame = trace_frame.get_exception_frame();
                let exception_record = ExceptionRecord::new(frame_num, exception_frame)
                    .expect("Error parsing exception_frame");
                exception_records.push(exception_record);
            }

            // update offset to point to next frame size
            mmap_offset += frame_size as usize;
        }

        println!("\rIndexing trace... done.");

        Ok(MoflowTrace {
            mmap: mmap,
            header: header,
            toc: toc,
            frame_idx: frame_idx,
            offset_to_frame: offset_to_frame,
            loaded_modules: loaded_modules,
            taint_intros: taint_intro_list,
            exception_records: exception_records,
            std_frame_idx: std_frame_idx,
        })
    }

    fn pp_std_frame(
        &self,
        std_frame: &frame::std_frame,
        frame_num: u64,
        cs: &mut capstone::Capstone,
    ) {
        let insns = cs
            .disasm_count(std_frame.get_rawbytes(), std_frame.get_address(), 1)
            .expect("disas fail");
        for insn in insns.iter() {
            if self.header.bfd_arch == 64 {
                println!(
                    "[{:5}] tid={:<5} addr 0x{:016x}: {} {}",
                    frame_num,
                    std_frame.get_thread_id(),
                    insn.address(),
                    insn.mnemonic().unwrap(),
                    insn.op_str().unwrap()
                );
            } else {
                println!("");
                let insn_string =
                    format!("{} {}", insn.mnemonic().unwrap(), insn.op_str().unwrap())
                        .to_uppercase();
                println!(
                    "[{:5}] tid={:<5} addr 0x{:08x}: {}",
                    frame_num,
                    std_frame.get_thread_id(),
                    insn.address(),
                    insn_string
                );
            }
        }
        println!("");
        self.pp_operand_info(std_frame.get_operand_pre_list().get_elem());
        //println!("");

        //these don't exist
        //println!("operand values after:");
        //pp_operand_info(std_frame.get_operand_post_list().get_elem());
    }

    fn get_operand_name(&self, opinfo: &frame::operand_info) -> String {
        let opinfo_spec = opinfo.get_operand_info_specific();
        if opinfo_spec.has_reg_operand() {
            format!("{} ", opinfo_spec.get_reg_operand().get_name().to_string())
        } else if opinfo_spec.has_mem_operand() {
            let operand = opinfo_spec.get_mem_operand();
            format!("MEM_0x{:<16X}", operand.get_address())
        } else {
            panic!("Unhandled operand")
        }
    }

    fn get_operand_access(&self, opinfo: &frame::operand_info) -> OperandAccess {
        let op_use = opinfo.get_operand_usage();
        if op_use.get_read() == true && op_use.get_written() == true {
            OperandAccess::ReadWrite
        } else if op_use.get_read() == true {
            OperandAccess::Read
        } else if op_use.get_written() == true {
            OperandAccess::Write
        } else {
            panic!("operand access");
        }
    }

    fn pp_operand_info_op(
        &self,
        info: &frame::operand_info,
    ) -> (String, OperandAccess, i64, i32, u64) {
        //let op_ssa_str = self.get_ssa_label(&self.get_operand_name(info));
        let op_str = self.get_operand_name(info);
        let op_access = self.get_operand_access(info);

        // get string indicating read/write/index/base
        let mut op_use_str = "".to_string();
        let op_use = info.get_operand_usage();
        if op_use.get_read() == true {
            op_use_str = format!("{} read  ", op_use_str);
        } else {
            op_use_str = format!("{}       ", op_use_str);
        }
        if op_use.get_written() == true {
            op_use_str = format!("{} write ", op_use_str);
        } else {
            op_use_str = format!("{}       ", op_use_str);
        }
        if op_use.get_index() == true {
            op_use_str = format!("{} index  ", op_use_str);
        }
        if op_use.get_base() == true {
            op_use_str = format!("{} base  ", op_use_str);
        }

        //let mut op_use_str = "".to_string();
        let op_taint = info.get_taint_info();
        let taint_id: i64;
        let taint_str = if op_taint.get_no_taint() == true {
            taint_id = 0;
            "no-taint".to_string()
        } else if op_taint.get_taint_id() != 0 {
            taint_id = op_taint.get_taint_id() as i64;
            format!("taint_id: {}", taint_id)
        } else if op_taint.get_taint_multiple() == true {
            taint_id = -1;
            "multi-taint".to_string()
        } else {
            panic!("taint info")
        };

        let bit_len = info.get_bit_length();

        let value = match bit_len {
            64 => Cursor::new(info.get_value())
                .read_u64::<LittleEndian>()
                .unwrap() as u64,
            32 => Cursor::new(info.get_value())
                .read_u32::<LittleEndian>()
                .unwrap() as u64,
            16 => Cursor::new(info.get_value())
                .read_u16::<LittleEndian>()
                .unwrap() as u64,
            8 => Cursor::new(info.get_value()).read_u8().unwrap() as u64,
            _ => 0,
        };

        /*
                if let Some(ssa_label) = self.ssa_labels.get(&op_str) {
                    op_str = ssa_label.to_string();
                } else {
                    let ssa_str = format!("{}_SSA", op_str).to_string();
                    self.ssa_labels.insert(op_str, ssa_str);
                }
        */
        //if op_taint.get_no_taint() == false && op_use.get_read() == true { taint_str = format!("{} TAINTED READ", taint_str)}
        println!(
            "        {:22} = {:16X}   {:2} bits   {:15} {}",
            op_str.to_string(),
            value,
            info.get_bit_length(),
            op_use_str,
            taint_str.to_string()
        );

        //println!("{:?}", info.get_operand_usage());
        //println!("{:?}", info.get_taint_info());

        return (op_str, op_access, taint_id, bit_len, value);
    }

    fn pp_operand_info(&self, op_info_list: &[frame::operand_info]) {
        // display read operands first
        for info in op_info_list {
            if info.get_operand_usage().get_read() == true {
                self.pp_operand_info_op(info);
            }
        }

        // display written operands second
        for info in op_info_list {
            // skip operands we displayed because they were read
            if info.get_operand_usage().get_written() == true
                && info.get_operand_usage().get_read() != true
            {
                self.pp_operand_info_op(info);
            }
        }

        /*
        These are not present in the trace?
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
    /*
        fn get_next_instruction() -> Option<(u64, frame::std_frame)>
        {

        }
    */

    fn addr_to_string(&self, address: u64) -> String {
        if self.header.bfd_arch == 64 {
            return format!("{:#016x}", address);
        } else {
            return format!("{:#08x}", address);
        }
    }

    fn pp_frame_range(
        &self,
        trace: &MoflowTrace,
        low: u64,
        high: u64,
        cs: &mut capstone::Capstone,
    ) {
        for i in low..high {
            self.pp_frame_num(trace, i, cs);
        }
    }

    fn pp_frame_num(&self, trace: &MoflowTrace, frame_num: u64, cs: &mut capstone::Capstone) {
        let (mmap_offset, frame_size) = self.frame_idx[frame_num as usize];
        let slice = &self.mmap[mmap_offset..(mmap_offset + frame_size as usize)];
        let trace_frame: frame::frame = parse_from_bytes::<frame::frame>(slice).unwrap();
        self.pp_frame(&trace_frame, frame_num, cs);
    }

    fn pp_frame(&self, trace_frame: &frame::frame, frame_num: u64, cs: &mut capstone::Capstone) {
        if trace_frame.has_modload_frame() {
            let modload_frame = trace_frame.get_modload_frame();
            let loaded_module =
                LoadedModule::new(frame_num, modload_frame).expect("Error parsing modload_frame");
            println!("");
            println!("[{:5}] Loaded module: {}", frame_num, loaded_module);
            return;
        }

        if trace_frame.has_taint_intro_frame() == true {
            let taint_intro_frame = trace_frame.get_taint_intro_frame();
            let taint_intro = TaintIntro::new(frame_num, taint_intro_frame)
                .expect("Error parsing taint_intro_frame");
            println!("");
            println!("[{:5}] {}", frame_num, taint_intro);
            //hexdump(taint_intro.data);
            return;
        }

        if trace_frame.has_exception_frame() == true {
            let exception_frame = trace_frame.get_exception_frame();
            let exception_record = ExceptionRecord::new(frame_num, exception_frame)
                .expect("Error parsing exception_frame");
            println!("");
            println!("[{:5}] {}", frame_num, exception_record);
            return;
        }

        if trace_frame.has_std_frame() {
            let std_frame = trace_frame.get_std_frame();
            self.pp_std_frame(std_frame, frame_num, cs);

            return;
        }

        if trace_frame.has_key_frame() {
            println!("{:?}", trace_frame.get_key_frame());
            //return;
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
            //return;
        }

        println!("");
        println!("XXXXXXXXXXXXXXXXX UNHANDLED FRAME XXXXXXXXXXXXXXXXXXXXX");
        fatal!("{:?}", trace_frame);

        return;
    }
}

/*
fn hexdump(data: Vec<u32>, display_addr: u64, indent: usize)
{
    let indent_str = format!("{:0width$}", "", width = indent);

    for offset in 0..data.len() {
        let byte = data[offset];
        print!("{:X?} ", byte);
        if offset % 16 == 0 {
            print!("\n{}{}", indent_str, addr_to_string(display_addr));
        }
    }
}
*/

fn pp_trace_header(trace: &MoflowTrace) {
    let header = &trace.header;
    println!("magic:   {:X}", header.magic_number);
    println!("version: {}", header.trace_version);
    let arch_str;
    match header.bfd_arch {
        BFD_ARCH_I386 => arch_str = "x86",
        _ => arch_str = "unknown",
    };
    let mach_str;
    match header.bfd_machine {
        BFD_MACH_I386_I386 => mach_str = "i386",
        BFD_MACH_X86_64 => mach_str = "X86_64",
        _ => mach_str = "unknown",
    };
    println!("arch:    {}", arch_str);
    println!("machine: {}", mach_str);
    //println!("toc offset:  {:?}", toc_offset);
    println!("frames:  {:?}", header.num_trace_frames);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("Usage: {} <moflow trace>", &args[0]);
        return;
    }

    let trace = MoflowTrace::new(&args[1]).expect("\nError: failed to load trace\n");

    let arch = match trace.header.bfd_arch {
        64 => arch::x86::ArchMode::Mode64,
        _ => arch::x86::ArchMode::Mode32,
        //32 => arch::x86::ArchMode::Mode32,
        //_ => panic!("Unknown arch found in header"),
    };

    let mut cs = Capstone::new()
        .x86()
        .mode(arch)
        .syntax(arch::x86::ArchSyntax::Intel)
        .detail(false)
        .build()
        .expect("Failed to create Capstone object");

    println!("# TRACE HEADER ################################################################");
    pp_trace_header(&trace);
    println!("##############################################################################");
    println!("");

    //
    let _toc_len = trace.toc.len();

    for module in &trace.loaded_modules {
        //println!("Loaded module: {}", module);
    }

    // print entire trace
    println!("# TRACE FRAMES ################################################################");
    trace.pp_frame_range(&trace, 0, trace.header.num_trace_frames, &mut cs);

    let header = &trace.header;

    let mut taint = TaintInfo::new();

    return;
}

// let hexes = HexSlice::new(str)
struct HexSlice<'a>(&'a [u8]);

impl<'a> HexSlice<'a> {
    fn new<T>(data: &'a T) -> HexSlice<'a>
    where
        T: ?Sized + AsRef<[u8]> + 'a,
    {
        HexSlice(data.as_ref())
    }
}

impl<'a> fmt::Display for HexSlice<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for byte in self.0 {
            write!(f, "{:X} ", byte)?;
        }
        Ok(())
    }
}
