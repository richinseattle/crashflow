/*All blocks must have two statements*/
/*All blocks must have two statements*/
/*All blocks must have two statements*/
/*ReadSyscall*/ @taint_intro 1, "file demo/input.txt", 0
  @context "mem32[0xdce75000]" = 0x41, 1, u8, wr
  @taint_intro 2, "file demo/input.txt", 1
  @context "mem32[0xdce75001]" = 0x41, 2, u8, wr
  @taint_intro 3, "file demo/input.txt", 2
  @context "mem32[0xdce75002]" = 0x41, 3, u8, wr
  @taint_intro 4, "file demo/input.txt", 3
  @context "mem32[0xdce75003]" = 0x41, 4, u8, wr
  @taint_intro 5, "file demo/input.txt", 4
  @context "mem32[0xdce75004]" = 0x41, 5, u8, wr
  @taint_intro 6, "file demo/input.txt", 5
  @context "mem32[0xdce75005]" = 0x41, 6, u8, wr
  @taint_intro 7, "file demo/input.txt", 6
  @context "mem32[0xdce75006]" = 0x41, 7, u8, wr
  @taint_intro 8, "file demo/input.txt", 7
  @context "mem32[0xdce75007]" = 0x41, 8, u8, wr
  @taint_intro 9, "file demo/input.txt", 8
  @context "mem32[0xdce75008]" = 0x41, 9, u8, wr
  @taint_intro 10, "file demo/input.txt", 9
  @context "mem32[0xdce75009]" = 0x41, 10, u8, wr
  @taint_intro 11, "file demo/input.txt", 10
  @context "mem32[0xdce7500a]" = 0x41, 11, u8, wr
  @taint_intro 12, "file demo/input.txt", 11
  @context "mem32[0xdce7500b]" = 0x41, 12, u8, wr
  @taint_intro 13, "file demo/input.txt", 12
  @context "mem32[0xdce7500c]" = 0x41, 13, u8, wr
  @taint_intro 14, "file demo/input.txt", 13
  @context "mem32[0xdce7500d]" = 0x41, 14, u8, wr
  @taint_intro 15, "file demo/input.txt", 14
  @context "mem32[0xdce7500e]" = 0x41, 15, u8, wr
  @taint_intro 16, "file demo/input.txt", 15
  @context "mem32[0xdce7500f]" = 0x41, 16, u8, wr
  @taint_intro 17, "file demo/input.txt", 16
  @context "mem32[0xdce75010]" = 0x41, 17, u8, wr
  @taint_intro 18, "file demo/input.txt", 17
  @context "mem32[0xdce75011]" = 0x41, 18, u8, wr
  @taint_intro 19, "file demo/input.txt", 18
  @context "mem32[0xdce75012]" = 0x41, 19, u8, wr
  @taint_intro 20, "file demo/input.txt", 19
  @context "mem32[0xdce75013]" = 0x41, 20, u8, wr
  @taint_intro 21, "file demo/input.txt", 20
  @context "mem32[0xdce75014]" = 0x41, 21, u8, wr
  @taint_intro 22, "file demo/input.txt", 21
  @context "mem32[0xdce75015]" = 0x41, 22, u8, wr
  @taint_intro 23, "file demo/input.txt", 22
  @context "mem32[0xdce75016]" = 0x41, 23, u8, wr
  @taint_intro 24, "file demo/input.txt", 23
  @context "mem32[0xdce75017]" = 0x41, 24, u8, wr
  @taint_intro 25, "file demo/input.txt", 24
  @context "mem32[0xdce75018]" = 0x41, 25, u8, wr
  @taint_intro 26, "file demo/input.txt", 25
  @context "mem32[0xdce75019]" = 0x41, 26, u8, wr
  @taint_intro 27, "file demo/input.txt", 26
  @context "mem32[0xdce7501a]" = 0x41, 27, u8, wr
  @taint_intro 28, "file demo/input.txt", 27
  @context "mem32[0xdce7501b]" = 0x41, 28, u8, wr
  @taint_intro 29, "file demo/input.txt", 28
  @context "mem32[0xdce7501c]" = 0x41, 29, u8, wr
  @taint_intro 30, "file demo/input.txt", 29
  @context "mem32[0xdce7501d]" = 0x41, 30, u8, wr
  @taint_intro 31, "file demo/input.txt", 30
  @context "mem32[0xdce7501e]" = 0x41, 31, u8, wr
  @taint_intro 32, "file demo/input.txt", 31
  @context "mem32[0xdce7501f]" = 0x41, 32, u8, wr
  @taint_intro 33, "file demo/input.txt", 32
  @context "mem32[0xdce75020]" = 0x41, 33, u8, wr
  @taint_intro 34, "file demo/input.txt", 33
  @context "mem32[0xdce75021]" = 0x41, 34, u8, wr
  @taint_intro 35, "file demo/input.txt", 34
  @context "mem32[0xdce75022]" = 0x41, 35, u8, wr
  @taint_intro 36, "file demo/input.txt", 35
  @context "mem32[0xdce75023]" = 0x41, 36, u8, wr
  @taint_intro 37, "file demo/input.txt", 36
  @context "mem32[0xdce75024]" = 0x41, 37, u8, wr
  @taint_intro 38, "file demo/input.txt", 37
  @context "mem32[0xdce75025]" = 0x41, 38, u8, wr
  @taint_intro 39, "file demo/input.txt", 38
  @context "mem32[0xdce75026]" = 0x41, 39, u8, wr
  @taint_intro 40, "file demo/input.txt", 39
  @context "mem32[0xdce75027]" = 0x41, 40, u8, wr
  @taint_intro 41, "file demo/input.txt", 40
  @context "mem32[0xdce75028]" = 0x41, 41, u8, wr
  @taint_intro 42, "file demo/input.txt", 41
  @context "mem32[0xdce75029]" = 0x41, 42, u8, wr
  @taint_intro 43, "file demo/input.txt", 42
  @context "mem32[0xdce7502a]" = 0x41, 43, u8, wr
  @taint_intro 44, "file demo/input.txt", 43
  @context "mem32[0xdce7502b]" = 0x41, 44, u8, wr
  @taint_intro 45, "file demo/input.txt", 44
  @context "mem32[0xdce7502c]" = 0x41, 45, u8, wr
  @taint_intro 46, "file demo/input.txt", 45
  @context "mem32[0xdce7502d]" = 0x41, 46, u8, wr
  @taint_intro 47, "file demo/input.txt", 46
  @context "mem32[0xdce7502e]" = 0x41, 47, u8, wr
  @taint_intro 48, "file demo/input.txt", 47
  @context "mem32[0xdce7502f]" = 0x41, 48, u8, wr
  @taint_intro 49, "file demo/input.txt", 48
  @context "mem32[0xdce75030]" = 0x41, 49, u8, wr
  @taint_intro 50, "file demo/input.txt", 49
  @context "mem32[0xdce75031]" = 0x41, 50, u8, wr
  @taint_intro 51, "file demo/input.txt", 50
  @context "mem32[0xdce75032]" = 0x41, 51, u8, wr
  @taint_intro 52, "file demo/input.txt", 51
  @context "mem32[0xdce75033]" = 0x41, 52, u8, wr
  @taint_intro 53, "file demo/input.txt", 52
  @context "mem32[0xdce75034]" = 0x41, 53, u8, wr
  @taint_intro 54, "file demo/input.txt", 53
  @context "mem32[0xdce75035]" = 0x41, 54, u8, wr
  @taint_intro 55, "file demo/input.txt", 54
  @context "mem32[0xdce75036]" = 0x41, 55, u8, wr
  @taint_intro 56, "file demo/input.txt", 55
  @context "mem32[0xdce75037]" = 0x41, 56, u8, wr
  @taint_intro 57, "file demo/input.txt", 56
  @context "mem32[0xdce75038]" = 0x41, 57, u8, wr
  @taint_intro 58, "file demo/input.txt", 57
  @context "mem32[0xdce75039]" = 0x41, 58, u8, wr
  @taint_intro 59, "file demo/input.txt", 58
  @context "mem32[0xdce7503a]" = 0x41, 59, u8, wr
  @taint_intro 60, "file demo/input.txt", 59
  @context "mem32[0xdce7503b]" = 0x41, 60, u8, wr
  @taint_intro 61, "file demo/input.txt", 60
  @context "mem32[0xdce7503c]" = 0x41, 61, u8, wr
  @taint_intro 62, "file demo/input.txt", 61
  @context "mem32[0xdce7503d]" = 0x41, 62, u8, wr
  @taint_intro 63, "file demo/input.txt", 62
  @context "mem32[0xdce7503e]" = 0x41, 63, u8, wr
  @taint_intro 64, "file demo/input.txt", 63
  @context "mem32[0xdce7503f]" = 0x41, 64, u8, wr
  @taint_intro 65, "file demo/input.txt", 64
  @context "mem32[0xdce75040]" = 0x41, 65, u8, wr
  @taint_intro 66, "file demo/input.txt", 65
  @context "mem32[0xdce75041]" = 0x41, 66, u8, wr
  @taint_intro 67, "file demo/input.txt", 66
  @context "mem32[0xdce75042]" = 0x41, 67, u8, wr
  @taint_intro 68, "file demo/input.txt", 67
  @context "mem32[0xdce75043]" = 0x41, 68, u8, wr
  @taint_intro 69, "file demo/input.txt", 68
  @context "mem32[0xdce75044]" = 0x41, 69, u8, wr
  @taint_intro 70, "file demo/input.txt", 69
  @context "mem32[0xdce75045]" = 0x41, 70, u8, wr
  @taint_intro 71, "file demo/input.txt", 70
  @context "mem32[0xdce75046]" = 0x41, 71, u8, wr
  @taint_intro 72, "file demo/input.txt", 71
  @context "mem32[0xdce75047]" = 0x41, 72, u8, wr
  @taint_intro 73, "file demo/input.txt", 72
  @context "mem32[0xdce75048]" = 0x41, 73, u8, wr
  @taint_intro 74, "file demo/input.txt", 73
  @context "mem32[0xdce75049]" = 0x41, 74, u8, wr
  @taint_intro 75, "file demo/input.txt", 74
  @context "mem32[0xdce7504a]" = 0x41, 75, u8, wr
  @taint_intro 76, "file demo/input.txt", 75
  @context "mem32[0xdce7504b]" = 0x41, 76, u8, wr
  @taint_intro 77, "file demo/input.txt", 76
  @context "mem32[0xdce7504c]" = 0x41, 77, u8, wr
  @taint_intro 78, "file demo/input.txt", 77
  @context "mem32[0xdce7504d]" = 0x41, 78, u8, wr
  @taint_intro 79, "file demo/input.txt", 78
  @context "mem32[0xdce7504e]" = 0x41, 79, u8, wr
  @taint_intro 80, "file demo/input.txt", 79
  @context "mem32[0xdce7504f]" = 0x41, 80, u8, wr
  @taint_intro 81, "file demo/input.txt", 80
  @context "mem32[0xdce75050]" = 0x41, 81, u8, wr
  @taint_intro 82, "file demo/input.txt", 81
  @context "mem32[0xdce75051]" = 0x41, 82, u8, wr
  @taint_intro 83, "file demo/input.txt", 82
  @context "mem32[0xdce75052]" = 0x41, 83, u8, wr
  @taint_intro 84, "file demo/input.txt", 83
  @context "mem32[0xdce75053]" = 0x41, 84, u8, wr
  @taint_intro 85, "file demo/input.txt", 84
  @context "mem32[0xdce75054]" = 0x41, 85, u8, wr
  @taint_intro 86, "file demo/input.txt", 85
  @context "mem32[0xdce75055]" = 0x41, 86, u8, wr
  @taint_intro 87, "file demo/input.txt", 86
  @context "mem32[0xdce75056]" = 0x41, 87, u8, wr
  @taint_intro 88, "file demo/input.txt", 87
  @context "mem32[0xdce75057]" = 0x41, 88, u8, wr
  @taint_intro 89, "file demo/input.txt", 88
  @context "mem32[0xdce75058]" = 0x41, 89, u8, wr
  @taint_intro 90, "file demo/input.txt", 89
  @context "mem32[0xdce75059]" = 0x41, 90, u8, wr
  @taint_intro 91, "file demo/input.txt", 90
  @context "mem32[0xdce7505a]" = 0x41, 91, u8, wr
  @taint_intro 92, "file demo/input.txt", 91
  @context "mem32[0xdce7505b]" = 0x41, 92, u8, wr
  @taint_intro 93, "file demo/input.txt", 92
  @context "mem32[0xdce7505c]" = 0x41, 93, u8, wr
  @taint_intro 94, "file demo/input.txt", 93
  @context "mem32[0xdce7505d]" = 0x41, 94, u8, wr
  @taint_intro 95, "file demo/input.txt", 94
  @context "mem32[0xdce7505e]" = 0x41, 95, u8, wr
  @taint_intro 96, "file demo/input.txt", 95
  @context "mem32[0xdce7505f]" = 0x41, 96, u8, wr
  @taint_intro 97, "file demo/input.txt", 96
  @context "mem32[0xdce75060]" = 0x41, 97, u8, wr
  @taint_intro 98, "file demo/input.txt", 97
  @context "mem32[0xdce75061]" = 0x41, 98, u8, wr
  @taint_intro 99, "file demo/input.txt", 98
  @context "mem32[0xdce75062]" = 0x41, 99, u8, wr
  @taint_intro 100, "file demo/input.txt", 99
  @context "mem32[0xdce75063]" = 0x41, 100, u8, wr
  @taint_intro 101, "file demo/input.txt", 100
  @context "mem32[0xdce75064]" = 0x41, 101, u8, wr
  @taint_intro 102, "file demo/input.txt", 101
  @context "mem32[0xdce75065]" = 0x41, 102, u8, wr
  @taint_intro 103, "file demo/input.txt", 102
  @context "mem32[0xdce75066]" = 0x41, 103, u8, wr
  @taint_intro 104, "file demo/input.txt", 103
  @context "mem32[0xdce75067]" = 0x41, 104, u8, wr
  @taint_intro 105, "file demo/input.txt", 104
  @context "mem32[0xdce75068]" = 0x41, 105, u8, wr
  @taint_intro 106, "file demo/input.txt", 105
  @context "mem32[0xdce75069]" = 0x41, 106, u8, wr
  @taint_intro 107, "file demo/input.txt", 106
  @context "mem32[0xdce7506a]" = 0x41, 107, u8, wr
  @taint_intro 108, "file demo/input.txt", 107
  @context "mem32[0xdce7506b]" = 0x41, 108, u8, wr
  @taint_intro 109, "file demo/input.txt", 108
  @context "mem32[0xdce7506c]" = 0x41, 109, u8, wr
  @taint_intro 110, "file demo/input.txt", 109
  @context "mem32[0xdce7506d]" = 0x41, 110, u8, wr
  @taint_intro 111, "file demo/input.txt", 110
  @context "mem32[0xdce7506e]" = 0x41, 111, u8, wr
  @taint_intro 112, "file demo/input.txt", 111
  @context "mem32[0xdce7506f]" = 0x41, 112, u8, wr
  @taint_intro 113, "file demo/input.txt", 112
  @context "mem32[0xdce75070]" = 0x41, 113, u8, wr
  @taint_intro 114, "file demo/input.txt", 113
  @context "mem32[0xdce75071]" = 0x41, 114, u8, wr
  @taint_intro 115, "file demo/input.txt", 114
  @context "mem32[0xdce75072]" = 0x41, 115, u8, wr
  @taint_intro 116, "file demo/input.txt", 115
  @context "mem32[0xdce75073]" = 0x41, 116, u8, wr
  @taint_intro 117, "file demo/input.txt", 116
  @context "mem32[0xdce75074]" = 0x41, 117, u8, wr
  @taint_intro 118, "file demo/input.txt", 117
  @context "mem32[0xdce75075]" = 0x41, 118, u8, wr
  @taint_intro 119, "file demo/input.txt", 118
  @context "mem32[0xdce75076]" = 0x41, 119, u8, wr
  @taint_intro 120, "file demo/input.txt", 119
  @context "mem32[0xdce75077]" = 0x41, 120, u8, wr
  @taint_intro 121, "file demo/input.txt", 120
  @context "mem32[0xdce75078]" = 0x41, 121, u8, wr
  @taint_intro 122, "file demo/input.txt", 121
  @context "mem32[0xdce75079]" = 0x41, 122, u8, wr
  @taint_intro 123, "file demo/input.txt", 122
  @context "mem32[0xdce7507a]" = 0x41, 123, u8, wr
  @taint_intro 124, "file demo/input.txt", 123
  @context "mem32[0xdce7507b]" = 0x41, 124, u8, wr
  @taint_intro 125, "file demo/input.txt", 124
  @context "mem32[0xdce7507c]" = 0x41, 125, u8, wr
  @taint_intro 126, "file demo/input.txt", 125
  @context "mem32[0xdce7507d]" = 0x41, 126, u8, wr
  @taint_intro 127, "file demo/input.txt", 126
  @context "mem32[0xdce7507e]" = 0x41, 127, u8, wr
  @taint_intro 128, "file demo/input.txt", 127
  @context "mem32[0xdce7507f]" = 0x41, 128, u8, wr
  @taint_intro 129, "file demo/input.txt", 128
  @context "mem32[0xdce75080]" = 0x41, 129, u8, wr
  @taint_intro 130, "file demo/input.txt", 129
  @context "mem32[0xdce75081]" = 0x41, 130, u8, wr
  @taint_intro 131, "file demo/input.txt", 130
  @context "mem32[0xdce75082]" = 0x41, 131, u8, wr
  @taint_intro 132, "file demo/input.txt", 131
  @context "mem32[0xdce75083]" = 0x41, 132, u8, wr
  @taint_intro 133, "file demo/input.txt", 132
  @context "mem32[0xdce75084]" = 0x41, 133, u8, wr
  @taint_intro 134, "file demo/input.txt", 133
  @context "mem32[0xdce75085]" = 0x41, 134, u8, wr
  @taint_intro 135, "file demo/input.txt", 134
  @context "mem32[0xdce75086]" = 0x41, 135, u8, wr
  @taint_intro 136, "file demo/input.txt", 135
  @context "mem32[0xdce75087]" = 0x41, 136, u8, wr
  @taint_intro 137, "file demo/input.txt", 136
  @context "mem32[0xdce75088]" = 0x41, 137, u8, wr
  @taint_intro 138, "file demo/input.txt", 137
  @context "mem32[0xdce75089]" = 0x41, 138, u8, wr
  @taint_intro 139, "file demo/input.txt", 138
  @context "mem32[0xdce7508a]" = 0x41, 139, u8, wr
  @taint_intro 140, "file demo/input.txt", 139
  @context "mem32[0xdce7508b]" = 0x41, 140, u8, wr
  @taint_intro 141, "file demo/input.txt", 140
  @context "mem32[0xdce7508c]" = 0x41, 141, u8, wr
  @taint_intro 142, "file demo/input.txt", 141
  @context "mem32[0xdce7508d]" = 0x41, 142, u8, wr
  @taint_intro 143, "file demo/input.txt", 142
  @context "mem32[0xdce7508e]" = 0x41, 143, u8, wr
  @taint_intro 144, "file demo/input.txt", 143
  @context "mem32[0xdce7508f]" = 0x41, 144, u8, wr
  @taint_intro 145, "file demo/input.txt", 144
  @context "mem32[0xdce75090]" = 0x41, 145, u8, wr
  @taint_intro 146, "file demo/input.txt", 145
  @context "mem32[0xdce75091]" = 0x41, 146, u8, wr
  @taint_intro 147, "file demo/input.txt", 146
  @context "mem32[0xdce75092]" = 0x41, 147, u8, wr
  @taint_intro 148, "file demo/input.txt", 147
  @context "mem32[0xdce75093]" = 0x41, 148, u8, wr
  @taint_intro 149, "file demo/input.txt", 148
  @context "mem32[0xdce75094]" = 0x41, 149, u8, wr
  @taint_intro 150, "file demo/input.txt", 149
  @context "mem32[0xdce75095]" = 0x41, 150, u8, wr
  @taint_intro 151, "file demo/input.txt", 150
  @context "mem32[0xdce75096]" = 0x41, 151, u8, wr
  @taint_intro 152, "file demo/input.txt", 151
  @context "mem32[0xdce75097]" = 0x41, 152, u8, wr
  @taint_intro 153, "file demo/input.txt", 152
  @context "mem32[0xdce75098]" = 0x41, 153, u8, wr
  @taint_intro 154, "file demo/input.txt", 153
  @context "mem32[0xdce75099]" = 0x41, 154, u8, wr
  @taint_intro 155, "file demo/input.txt", 154
  @context "mem32[0xdce7509a]" = 0x41, 155, u8, wr
  @taint_intro 156, "file demo/input.txt", 155
  @context "mem32[0xdce7509b]" = 0x41, 156, u8, wr
  @taint_intro 157, "file demo/input.txt", 156
  @context "mem32[0xdce7509c]" = 0x41, 157, u8, wr
  @taint_intro 158, "file demo/input.txt", 157
  @context "mem32[0xdce7509d]" = 0x41, 158, u8, wr
  @taint_intro 159, "file demo/input.txt", 158
  @context "mem32[0xdce7509e]" = 0x41, 159, u8, wr
  @taint_intro 160, "file demo/input.txt", 159
  @context "mem32[0xdce7509f]" = 0x41, 160, u8, wr
  @taint_intro 161, "file demo/input.txt", 160
  @context "mem32[0xdce750a0]" = 0x41, 161, u8, wr
  @taint_intro 162, "file demo/input.txt", 161
  @context "mem32[0xdce750a1]" = 0x41, 162, u8, wr
  @taint_intro 163, "file demo/input.txt", 162
  @context "mem32[0xdce750a2]" = 0x41, 163, u8, wr
  @taint_intro 164, "file demo/input.txt", 163
  @context "mem32[0xdce750a3]" = 0x41, 164, u8, wr
  @taint_intro 165, "file demo/input.txt", 164
  @context "mem32[0xdce750a4]" = 0x41, 165, u8, wr
  @taint_intro 166, "file demo/input.txt", 165
  @context "mem32[0xdce750a5]" = 0x41, 166, u8, wr
  @taint_intro 167, "file demo/input.txt", 166
  @context "mem32[0xdce750a6]" = 0x41, 167, u8, wr
  @taint_intro 168, "file demo/input.txt", 167
  @context "mem32[0xdce750a7]" = 0x41, 168, u8, wr
  @taint_intro 169, "file demo/input.txt", 168
  @context "mem32[0xdce750a8]" = 0x41, 169, u8, wr
  @taint_intro 170, "file demo/input.txt", 169
  @context "mem32[0xdce750a9]" = 0x41, 170, u8, wr
  @taint_intro 171, "file demo/input.txt", 170
  @context "mem32[0xdce750aa]" = 0x41, 171, u8, wr
  @taint_intro 172, "file demo/input.txt", 171
  @context "mem32[0xdce750ab]" = 0x41, 172, u8, wr
  @taint_intro 173, "file demo/input.txt", 172
  @context "mem32[0xdce750ac]" = 0x41, 173, u8, wr
  @taint_intro 174, "file demo/input.txt", 173
  @context "mem32[0xdce750ad]" = 0x41, 174, u8, wr
  @taint_intro 175, "file demo/input.txt", 174
  @context "mem32[0xdce750ae]" = 0x41, 175, u8, wr
  @taint_intro 176, "file demo/input.txt", 175
  @context "mem32[0xdce750af]" = 0x41, 176, u8, wr
  @taint_intro 177, "file demo/input.txt", 176
  @context "mem32[0xdce750b0]" = 0x41, 177, u8, wr
  @taint_intro 178, "file demo/input.txt", 177
  @context "mem32[0xdce750b1]" = 0x41, 178, u8, wr
  @taint_intro 179, "file demo/input.txt", 178
  @context "mem32[0xdce750b2]" = 0x41, 179, u8, wr
  @taint_intro 180, "file demo/input.txt", 179
  @context "mem32[0xdce750b3]" = 0x41, 180, u8, wr
  @taint_intro 181, "file demo/input.txt", 180
  @context "mem32[0xdce750b4]" = 0x41, 181, u8, wr
  @taint_intro 182, "file demo/input.txt", 181
  @context "mem32[0xdce750b5]" = 0x41, 182, u8, wr
  @taint_intro 183, "file demo/input.txt", 182
  @context "mem32[0xdce750b6]" = 0x41, 183, u8, wr
  @taint_intro 184, "file demo/input.txt", 183
  @context "mem32[0xdce750b7]" = 0x41, 184, u8, wr
  @taint_intro 185, "file demo/input.txt", 184
  @context "mem32[0xdce750b8]" = 0x41, 185, u8, wr
  @taint_intro 186, "file demo/input.txt", 185
  @context "mem32[0xdce750b9]" = 0x41, 186, u8, wr
  @taint_intro 187, "file demo/input.txt", 186
  @context "mem32[0xdce750ba]" = 0x41, 187, u8, wr
  @taint_intro 188, "file demo/input.txt", 187
  @context "mem32[0xdce750bb]" = 0x41, 188, u8, wr
  @taint_intro 189, "file demo/input.txt", 188
  @context "mem32[0xdce750bc]" = 0x41, 189, u8, wr
  @taint_intro 190, "file demo/input.txt", 189
  @context "mem32[0xdce750bd]" = 0x41, 190, u8, wr
  @taint_intro 191, "file demo/input.txt", 190
  @context "mem32[0xdce750be]" = 0x41, 191, u8, wr
  @taint_intro 192, "file demo/input.txt", 191
  @context "mem32[0xdce750bf]" = 0x41, 192, u8, wr
  @taint_intro 193, "file demo/input.txt", 192
  @context "mem32[0xdce750c0]" = 0x41, 193, u8, wr
  @taint_intro 194, "file demo/input.txt", 193
  @context "mem32[0xdce750c1]" = 0x41, 194, u8, wr
  @taint_intro 195, "file demo/input.txt", 194
  @context "mem32[0xdce750c2]" = 0x41, 195, u8, wr
  @taint_intro 196, "file demo/input.txt", 195
  @context "mem32[0xdce750c3]" = 0x41, 196, u8, wr
  @taint_intro 197, "file demo/input.txt", 196
  @context "mem32[0xdce750c4]" = 0x41, 197, u8, wr
  @taint_intro 198, "file demo/input.txt", 197
  @context "mem32[0xdce750c5]" = 0x41, 198, u8, wr
  @taint_intro 199, "file demo/input.txt", 198
  @context "mem32[0xdce750c6]" = 0x41, 199, u8, wr
  @taint_intro 200, "file demo/input.txt", 199
  @context "mem32[0xdce750c7]" = 0x41, 200, u8, wr
  @taint_intro 201, "file demo/input.txt", 200
  @context "mem32[0xdce750c8]" = 0x41, 201, u8, wr
  @taint_intro 202, "file demo/input.txt", 201
  @context "mem32[0xdce750c9]" = 0x41, 202, u8, wr
  @taint_intro 203, "file demo/input.txt", 202
  @context "mem32[0xdce750ca]" = 0x41, 203, u8, wr
  @taint_intro 204, "file demo/input.txt", 203
  @context "mem32[0xdce750cb]" = 0x41, 204, u8, wr
  @taint_intro 205, "file demo/input.txt", 204
  @context "mem32[0xdce750cc]" = 0x41, 205, u8, wr
  @taint_intro 206, "file demo/input.txt", 205
  @context "mem32[0xdce750cd]" = 0x41, 206, u8, wr
  @taint_intro 207, "file demo/input.txt", 206
  @context "mem32[0xdce750ce]" = 0x41, 207, u8, wr
  @taint_intro 208, "file demo/input.txt", 207
  @context "mem32[0xdce750cf]" = 0x41, 208, u8, wr
  @taint_intro 209, "file demo/input.txt", 208
  @context "mem32[0xdce750d0]" = 0x41, 209, u8, wr
  @taint_intro 210, "file demo/input.txt", 209
  @context "mem32[0xdce750d1]" = 0x41, 210, u8, wr
  @taint_intro 211, "file demo/input.txt", 210
  @context "mem32[0xdce750d2]" = 0x41, 211, u8, wr
  @taint_intro 212, "file demo/input.txt", 211
  @context "mem32[0xdce750d3]" = 0x41, 212, u8, wr
  @taint_intro 213, "file demo/input.txt", 212
  @context "mem32[0xdce750d4]" = 0x41, 213, u8, wr
  @taint_intro 214, "file demo/input.txt", 213
  @context "mem32[0xdce750d5]" = 0xa, 214, u8, wr
/*All blocks must have two statements*/
dsa_mem_dce75000_1_2140:u8 = symb_1_679:u8
dsa_mem_dce75001_1_2141:u8 = symb_2_681:u8
dsa_mem_dce75002_1_2142:u8 = symb_3_683:u8
dsa_mem_dce75003_1_2143:u8 = symb_4_685:u8
dsa_mem_dce75004_1_2144:u8 = symb_5_687:u8
dsa_mem_dce75005_1_2145:u8 = symb_6_689:u8
dsa_mem_dce75006_1_2146:u8 = symb_7_691:u8
dsa_mem_dce75007_1_2147:u8 = symb_8_693:u8
dsa_mem_dce75008_1_2148:u8 = symb_9_695:u8
dsa_mem_dce75009_1_2149:u8 = symb_10_697:u8
dsa_mem_dce7500a_1_2150:u8 = symb_11_699:u8
dsa_mem_dce7500b_1_2151:u8 = symb_12_701:u8
dsa_mem_dce7500c_1_2152:u8 = symb_13_703:u8
dsa_mem_dce7500d_1_2153:u8 = symb_14_705:u8
dsa_mem_dce7500e_1_2154:u8 = symb_15_707:u8
dsa_mem_dce7500f_1_2155:u8 = symb_16_709:u8
dsa_mem_dce75010_1_2156:u8 = symb_17_711:u8
dsa_mem_dce75011_1_2157:u8 = symb_18_713:u8
dsa_mem_dce75012_1_2158:u8 = symb_19_715:u8
dsa_mem_dce75013_1_2159:u8 = symb_20_717:u8
dsa_mem_dce75014_1_2160:u8 = symb_21_719:u8
dsa_mem_dce75015_1_2161:u8 = symb_22_721:u8
dsa_mem_dce75016_1_2162:u8 = symb_23_723:u8
dsa_mem_dce75017_1_2163:u8 = symb_24_725:u8
dsa_mem_dce75018_1_2164:u8 = symb_25_727:u8
dsa_mem_dce75019_1_2165:u8 = symb_26_729:u8
dsa_mem_dce7501a_1_2166:u8 = symb_27_731:u8
dsa_mem_dce7501b_1_2167:u8 = symb_28_733:u8
dsa_mem_dce7501c_1_2168:u8 = symb_29_735:u8
dsa_mem_dce7501d_1_2169:u8 = symb_30_737:u8
dsa_mem_dce7501e_1_2170:u8 = symb_31_739:u8
dsa_mem_dce7501f_1_2171:u8 = symb_32_741:u8
dsa_mem_dce75020_1_2172:u8 = symb_33_743:u8
dsa_mem_dce75021_1_2173:u8 = symb_34_745:u8
dsa_mem_dce75022_1_2174:u8 = symb_35_747:u8
dsa_mem_dce75023_1_2175:u8 = symb_36_749:u8
dsa_mem_dce75024_1_2176:u8 = symb_37_751:u8
dsa_mem_dce75025_1_2177:u8 = symb_38_753:u8
dsa_mem_dce75026_1_2178:u8 = symb_39_755:u8
dsa_mem_dce75027_1_2179:u8 = symb_40_757:u8
dsa_mem_dce75028_1_2180:u8 = symb_41_759:u8
dsa_mem_dce75029_1_2181:u8 = symb_42_761:u8
dsa_mem_dce7502a_1_2182:u8 = symb_43_763:u8
dsa_mem_dce7502b_1_2183:u8 = symb_44_765:u8
dsa_mem_dce7502c_1_2184:u8 = symb_45_767:u8
dsa_mem_dce7502d_1_2185:u8 = symb_46_769:u8
dsa_mem_dce7502e_1_2186:u8 = symb_47_771:u8
dsa_mem_dce7502f_1_2187:u8 = symb_48_773:u8
dsa_mem_dce75030_1_2188:u8 = symb_49_775:u8
dsa_mem_dce75031_1_2189:u8 = symb_50_777:u8
dsa_mem_dce75032_1_2190:u8 = symb_51_779:u8
dsa_mem_dce75033_1_2191:u8 = symb_52_781:u8
dsa_mem_dce75034_1_2192:u8 = symb_53_783:u8
dsa_mem_dce75035_1_2193:u8 = symb_54_785:u8
dsa_mem_dce75036_1_2194:u8 = symb_55_787:u8
dsa_mem_dce75037_1_2195:u8 = symb_56_789:u8
dsa_mem_dce75038_1_2196:u8 = symb_57_791:u8
dsa_mem_dce75039_1_2197:u8 = symb_58_793:u8
dsa_mem_dce7503a_1_2198:u8 = symb_59_795:u8
dsa_mem_dce7503b_1_2199:u8 = symb_60_797:u8
dsa_mem_dce7503c_1_2200:u8 = symb_61_799:u8
dsa_mem_dce7503d_1_2201:u8 = symb_62_801:u8
dsa_mem_dce7503e_1_2202:u8 = symb_63_803:u8
dsa_mem_dce7503f_1_2203:u8 = symb_64_805:u8
dsa_mem_dce75040_1_2204:u8 = symb_65_807:u8
dsa_mem_dce75041_1_2205:u8 = symb_66_809:u8
dsa_mem_dce75042_1_2206:u8 = symb_67_811:u8
dsa_mem_dce75043_1_2207:u8 = symb_68_813:u8
dsa_mem_dce75044_1_2208:u8 = symb_69_815:u8
dsa_mem_dce75045_1_2209:u8 = symb_70_817:u8
dsa_mem_dce75046_1_2210:u8 = symb_71_819:u8
dsa_mem_dce75047_1_2211:u8 = symb_72_821:u8
dsa_mem_dce75048_1_2212:u8 = symb_73_823:u8
dsa_mem_dce75049_1_2213:u8 = symb_74_825:u8
dsa_mem_dce7504a_1_2214:u8 = symb_75_827:u8
dsa_mem_dce7504b_1_2215:u8 = symb_76_829:u8
dsa_mem_dce7504c_1_2216:u8 = symb_77_831:u8
dsa_mem_dce7504d_1_2217:u8 = symb_78_833:u8
dsa_mem_dce7504e_1_2218:u8 = symb_79_835:u8
dsa_mem_dce7504f_1_2219:u8 = symb_80_837:u8
dsa_mem_dce75050_1_2220:u8 = symb_81_839:u8
dsa_mem_dce75051_1_2221:u8 = symb_82_841:u8
dsa_mem_dce75052_1_2222:u8 = symb_83_843:u8
dsa_mem_dce75053_1_2223:u8 = symb_84_845:u8
dsa_mem_dce75054_1_2224:u8 = symb_85_847:u8
dsa_mem_dce75055_1_2225:u8 = symb_86_849:u8
dsa_mem_dce75056_1_2226:u8 = symb_87_851:u8
dsa_mem_dce75057_1_2227:u8 = symb_88_853:u8
dsa_mem_dce75058_1_2228:u8 = symb_89_855:u8
dsa_mem_dce75059_1_2229:u8 = symb_90_857:u8
dsa_mem_dce7505a_1_2230:u8 = symb_91_859:u8
dsa_mem_dce7505b_1_2231:u8 = symb_92_861:u8
dsa_mem_dce7505c_1_2232:u8 = symb_93_863:u8
dsa_mem_dce7505d_1_2233:u8 = symb_94_865:u8
dsa_mem_dce7505e_1_2234:u8 = symb_95_867:u8
dsa_mem_dce7505f_1_2235:u8 = symb_96_869:u8
dsa_mem_dce75060_1_2236:u8 = symb_97_871:u8
dsa_mem_dce75061_1_2237:u8 = symb_98_873:u8
dsa_mem_dce75062_1_2238:u8 = symb_99_875:u8
dsa_mem_dce75063_1_2239:u8 = symb_100_877:u8
dsa_mem_dce75064_1_2240:u8 = symb_101_879:u8
dsa_mem_dce75065_1_2241:u8 = symb_102_881:u8
dsa_mem_dce75066_1_2242:u8 = symb_103_883:u8
dsa_mem_dce75067_1_2243:u8 = symb_104_885:u8
dsa_mem_dce75068_1_2244:u8 = symb_105_887:u8
dsa_mem_dce75069_1_2245:u8 = symb_106_889:u8
dsa_mem_dce7506a_1_2246:u8 = symb_107_891:u8
dsa_mem_dce7506b_1_2247:u8 = symb_108_893:u8
dsa_mem_dce7506c_1_2248:u8 = symb_109_895:u8
dsa_mem_dce7506d_1_2249:u8 = symb_110_897:u8
dsa_mem_dce7506e_1_2250:u8 = symb_111_899:u8
dsa_mem_dce7506f_1_2251:u8 = symb_112_901:u8
dsa_mem_dce75070_1_2252:u8 = symb_113_903:u8
dsa_mem_dce75071_1_2253:u8 = symb_114_905:u8
dsa_mem_dce75072_1_2254:u8 = symb_115_907:u8
dsa_mem_dce75073_1_2255:u8 = symb_116_909:u8
dsa_mem_dce75074_1_2256:u8 = symb_117_911:u8
dsa_mem_dce75075_1_2257:u8 = symb_118_913:u8
dsa_mem_dce75076_1_2258:u8 = symb_119_915:u8
dsa_mem_dce75077_1_2259:u8 = symb_120_917:u8
dsa_mem_dce75078_1_2260:u8 = symb_121_919:u8
dsa_mem_dce75079_1_2261:u8 = symb_122_921:u8
dsa_mem_dce7507a_1_2262:u8 = symb_123_923:u8
dsa_mem_dce7507b_1_2263:u8 = symb_124_925:u8
dsa_mem_dce7507c_1_2264:u8 = symb_125_927:u8
dsa_mem_dce7507d_1_2265:u8 = symb_126_929:u8
dsa_mem_dce7507e_1_2266:u8 = symb_127_931:u8
dsa_mem_dce7507f_1_2267:u8 = symb_128_933:u8
dsa_mem_dce75080_1_2268:u8 = symb_129_935:u8
dsa_mem_dce75081_1_2269:u8 = symb_130_937:u8
dsa_mem_dce75082_1_2270:u8 = symb_131_939:u8
dsa_mem_dce75083_1_2271:u8 = symb_132_941:u8
dsa_mem_dce75084_1_2272:u8 = symb_133_943:u8
dsa_mem_dce75085_1_2273:u8 = symb_134_945:u8
dsa_mem_dce75086_1_2274:u8 = symb_135_947:u8
dsa_mem_dce75087_1_2275:u8 = symb_136_949:u8
dsa_mem_dce75088_1_2276:u8 = symb_137_951:u8
dsa_mem_dce75089_1_2277:u8 = symb_138_953:u8
dsa_mem_dce7508a_1_2278:u8 = symb_139_955:u8
dsa_mem_dce7508b_1_2279:u8 = symb_140_957:u8
dsa_mem_dce7508c_1_2280:u8 = symb_141_959:u8
dsa_mem_dce7508d_1_2281:u8 = symb_142_961:u8
dsa_mem_dce7508e_1_2282:u8 = symb_143_963:u8
dsa_mem_dce7508f_1_2283:u8 = symb_144_965:u8
dsa_mem_dce75090_1_2284:u8 = symb_145_967:u8
dsa_mem_dce75091_1_2285:u8 = symb_146_969:u8
dsa_mem_dce75092_1_2286:u8 = symb_147_971:u8
dsa_mem_dce75093_1_2287:u8 = symb_148_973:u8
dsa_mem_dce75094_1_2288:u8 = symb_149_975:u8
dsa_mem_dce75095_1_2289:u8 = symb_150_977:u8
dsa_mem_dce75096_1_2290:u8 = symb_151_979:u8
dsa_mem_dce75097_1_2291:u8 = symb_152_981:u8
dsa_mem_dce75098_1_2292:u8 = symb_153_983:u8
dsa_mem_dce75099_1_2293:u8 = symb_154_985:u8
dsa_mem_dce7509a_1_2294:u8 = symb_155_987:u8
dsa_mem_dce7509b_1_2295:u8 = symb_156_989:u8
dsa_mem_dce7509c_1_2296:u8 = symb_157_991:u8
dsa_mem_dce7509d_1_2297:u8 = symb_158_993:u8
dsa_mem_dce7509e_1_2298:u8 = symb_159_995:u8
dsa_mem_dce7509f_1_2299:u8 = symb_160_997:u8
dsa_mem_dce750a0_1_2300:u8 = symb_161_999:u8
dsa_mem_dce750a1_1_2301:u8 = symb_162_1001:u8
dsa_mem_dce750a2_1_2302:u8 = symb_163_1003:u8
dsa_mem_dce750a3_1_2303:u8 = symb_164_1005:u8
dsa_mem_dce750a4_1_2304:u8 = symb_165_1007:u8
dsa_mem_dce750a5_1_2305:u8 = symb_166_1009:u8
dsa_mem_dce750a6_1_2306:u8 = symb_167_1011:u8
dsa_mem_dce750a7_1_2307:u8 = symb_168_1013:u8
dsa_mem_dce750a8_1_2308:u8 = symb_169_1015:u8
dsa_mem_dce750a9_1_2309:u8 = symb_170_1017:u8
dsa_mem_dce750aa_1_2310:u8 = symb_171_1019:u8
dsa_mem_dce750ab_1_2311:u8 = symb_172_1021:u8
dsa_mem_dce750ac_1_2312:u8 = symb_173_1023:u8
dsa_mem_dce750ad_1_2313:u8 = symb_174_1025:u8
dsa_mem_dce750ae_1_2314:u8 = symb_175_1027:u8
dsa_mem_dce750af_1_2315:u8 = symb_176_1029:u8
dsa_mem_dce750b0_1_2316:u8 = symb_177_1031:u8
dsa_mem_dce750b1_1_2317:u8 = symb_178_1033:u8
dsa_mem_dce750b2_1_2318:u8 = symb_179_1035:u8
dsa_mem_dce750b3_1_2319:u8 = symb_180_1037:u8
dsa_mem_dce750b4_1_2320:u8 = symb_181_1039:u8
dsa_mem_dce750b5_1_2321:u8 = symb_182_1041:u8
dsa_mem_dce750b6_1_2322:u8 = symb_183_1043:u8
dsa_mem_dce750b7_1_2323:u8 = symb_184_1045:u8
dsa_mem_dce750b8_1_2324:u8 = symb_185_1047:u8
dsa_mem_dce750b9_1_2325:u8 = symb_186_1049:u8
dsa_mem_dce750ba_1_2326:u8 = symb_187_1051:u8
dsa_mem_dce750bb_1_2327:u8 = symb_188_1053:u8
dsa_mem_dce750bc_1_2328:u8 = symb_189_1055:u8
dsa_mem_dce750bd_1_2329:u8 = symb_190_1057:u8
dsa_mem_dce750be_1_2330:u8 = symb_191_1059:u8
dsa_mem_dce750bf_1_2331:u8 = symb_192_1061:u8
dsa_mem_dce750c0_1_2332:u8 = symb_193_1063:u8
dsa_mem_dce750c1_1_2333:u8 = symb_194_1065:u8
dsa_mem_dce750c2_1_2334:u8 = symb_195_1067:u8
dsa_mem_dce750c3_1_2335:u8 = symb_196_1069:u8
dsa_mem_dce750c4_1_2336:u8 = symb_197_1071:u8
dsa_mem_dce750c5_1_2337:u8 = symb_198_1073:u8
dsa_mem_dce750c6_1_2338:u8 = symb_199_1075:u8
dsa_mem_dce750c7_1_2339:u8 = symb_200_1077:u8
dsa_mem_dce750c8_1_2340:u8 = symb_201_1079:u8
dsa_mem_dce750c9_1_2341:u8 = symb_202_1081:u8
dsa_mem_dce750ca_1_2342:u8 = symb_203_1083:u8
dsa_mem_dce750cb_1_2343:u8 = symb_204_1085:u8
dsa_mem_dce750cc_1_2344:u8 = symb_205_1087:u8
dsa_mem_dce750cd_1_2345:u8 = symb_206_1089:u8
dsa_mem_dce750ce_1_2346:u8 = symb_207_1091:u8
dsa_mem_dce750cf_1_2347:u8 = symb_208_1093:u8
dsa_mem_dce750d0_1_2348:u8 = symb_209_1095:u8
dsa_mem_dce750d1_1_2349:u8 = symb_210_1097:u8
dsa_mem_dce750d2_1_2350:u8 = symb_211_1099:u8
dsa_mem_dce750d3_1_2351:u8 = symb_212_1101:u8
dsa_mem_dce750d4_1_2352:u8 = symb_213_1103:u8
dsa_mem_dce750d5_1_2353:u8 = symb_214_1105:u8
addr 0xdcf2fe28 @asm "movzx  eax,BYTE PTR [eax]" @tid "0"
  @context "R_EAX_32" = 0xdce75000, 0, u32, wr
  @context "R_EAX_32" = 0xdce75000, 0, u32, rd
  @context "mem32[0xdce75000]" = 0x41, 1, u8, rd
label pc_0xdcf2fe28
dsa_R_EAX_32_1_2354:u32 = 0xdce75000:u32
dsa_R_EAX_32_1_2355:u32 = pad:u32(pad:u8(dsa_mem_dce75000_1_2140:u8))
addr 0xdcf2f038 @asm "cmp    eax,0xffffffff" @tid "0"
  @context "R_EAX_32" = 0x41, 1, u32, rd
  @context "R_EFLAGS" = 0x282, 0, u32, wr
label pc_0xdcf2f038
dsa_R_ZF_1_2356:bool = false
dsa_R_AF_1_2357:bool = false
dsa_R_OF_1_2358:bool = false
dsa_R_SF_1_2359:bool = true
dsa_R_DF_1_2360:bool = false
dsa_R_CF_1_2361:bool = false
dsa_R_EFLAGS_1_2362:u32 = 0x282:u32
dsa_R_PF_1_2363:bool = false
dsa_T_t_1_2364:u32 = dsa_R_EAX_32_1_2355:u32 - -1:u32
dsa_R_CF_1_2365:bool = dsa_R_EAX_32_1_2355:u32 < -1:u32
dsa_R_OF_1_2366:bool =
  high:bool((dsa_R_EAX_32_1_2355:u32 ^ -1:u32) &
            (dsa_R_EAX_32_1_2355:u32 ^ dsa_T_t_1_2364:u32))
dsa_R_AF_1_2367:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_T_t_1_2364:u32 ^ dsa_R_EAX_32_1_2355:u32 ^ -1:u32))
dsa_R_PF_3_2370:bool =
  ~low:bool(let dsa_T_acc_1_2368:u32 :=
                                         dsa_T_t_1_2364:u32 >> 4:u32 ^
                                         dsa_T_t_1_2364:u32 in
            let dsa_T_acc_2_2369:u32 :=
                                         dsa_T_acc_1_2368:u32 >> 2:u32 ^
                                         dsa_T_acc_1_2368:u32 in
            dsa_T_acc_2_2369:u32 >> 1:u32 ^ dsa_T_acc_2_2369:u32)
dsa_R_SF_1_2371:bool = high:bool(dsa_T_t_1_2364:u32)
dsa_R_ZF_1_2372:bool = 0:u32 == dsa_T_t_1_2364:u32
addr 0xdcf2f03b @asm "jne    0x00000000dcf2ef76" @tid "0"
  @context "R_EIP" = 0xdcf2f03b, 0, u32, rw
  @context "R_EFLAGS" = 0x217, 1, u32, rd
label pc_0xdcf2f03b
dsa_R_DF_1_2373:bool = false
dsa_R_EIP_1_2374:u32 = 0xdcf2f03b:u32
assert ~dsa_R_ZF_1_2372:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf2ef76:u32, "nocjmp0"*/
addr 0xdcf2ef76 @asm "test   esi,esi" @tid "0"
  @context "R_ESI_32" = 0x400, 0, u32, rd
  @context "R_ESI_32" = 0x400, 0, u32, rd
  @context "R_EFLAGS" = 0x217, 1, u32, wr
label pc_0xdcf2ef76
dsa_R_ESI_32_1_2375:u32 = 0x400:u32
dsa_R_DF_1_2376:bool = false
dsa_T_t_1_2377:u32 = dsa_R_ESI_32_1_2375:u32 & dsa_R_ESI_32_1_2375:u32
dsa_R_OF_1_2378:bool = false
dsa_R_CF_1_2379:bool = false
dsa_R_AF_1_2380:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_2383:bool =
  ~low:bool(let dsa_T_acc_1_2381:u32 :=
                                         dsa_T_t_1_2377:u32 >> 4:u32 ^
                                         dsa_T_t_1_2377:u32 in
            let dsa_T_acc_2_2382:u32 :=
                                         dsa_T_acc_1_2381:u32 >> 2:u32 ^
                                         dsa_T_acc_1_2381:u32 in
            dsa_T_acc_2_2382:u32 >> 1:u32 ^ dsa_T_acc_2_2382:u32)
dsa_R_SF_1_2384:bool = high:bool(dsa_T_t_1_2377:u32)
dsa_R_ZF_1_2385:bool = 0:u32 == dsa_T_t_1_2377:u32
addr 0xdcf2eec0 @asm "mov    eax,DWORD PTR [ebp+0x4]" @tid "0"
  @context "R_EAX_32" = 0x41, 1, u32, wr
  @context "R_EBP_32" = 0x8656008, 0, u32, rd
  @context "mem32[0x865600c]" = 0x0, 0, u8, rd
  @context "mem32[0x865600d]" = 0x50, 0, u8, rd
  @context "mem32[0x865600e]" = 0xe7, 0, u8, rd
  @context "mem32[0x865600f]" = 0xdc, 0, u8, rd
label pc_0xdcf2eec0
dsa_mem_865600d_1_2386:u8 = low:u8(0x50:u8)
dsa_mem_865600c_1_2387:u8 = low:u8(0:u8)
dsa_mem_865600e_1_2388:u8 = low:u8(0xe7:u8)
dsa_mem_865600f_1_2389:u8 = low:u8(0xdc:u8)
dsa_R_EBP_32_1_2390:u32 = 0x8656008:u32
dsa_R_EAX_32_1_2391:u32 =
  pad:u32(dsa_mem_865600f_1_2389:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_865600e_1_2388:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_865600d_1_2386:u8) << 8:u32 |
  pad:u32(dsa_mem_865600c_1_2387:u8)))
addr 0xdcf3cc3a @asm "movs   WORD PTR es:[edi],WORD PTR ds:[esi]" @tid "0"
  @context "R_EDI_32" = 0xffaf071c, 0, u32, rd
  @context "R_ESI_32" = 0xdce75000, 0, u32, rd
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75000]" = 0x41, 1, u8, rd
  @context "mem32[0xdce75001]" = 0x41, 2, u8, rd
  @context "mem32[0xffaf071c]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf071d]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3a
dsa_mem_ffaf071c_1_2392:u8 = low:u8(0:u8)
dsa_mem_ffaf071d_1_2393:u8 = low:u8(0:u8)
dsa_R_ZF_1_2394:bool = false
dsa_R_ESI_32_1_2395:u32 = 0xdce75000:u32
dsa_R_AF_1_2396:bool = false
dsa_R_OF_1_2397:bool = false
dsa_R_SF_1_2398:bool = false
dsa_R_DF_1_2399:bool = false
dsa_R_EDI_32_1_2400:u32 = 0xffaf071c:u32
dsa_R_CF_1_2401:bool = true
dsa_R_EFLAGS_1_2402:u32 = 0x207:u32
dsa_R_PF_1_2403:bool = true
dsa_mem_ffaf071c_1_2404:u8 =
  low:u8(pad:u16(dsa_mem_dce75001_1_2141:u8) << 8:u16 |
         pad:u16(dsa_mem_dce75000_1_2140:u8))
dsa_mem_ffaf071d_1_2405:u8 =
  low:u8((pad:u16(dsa_mem_dce75001_1_2141:u8) << 8:u16 |
         pad:u16(dsa_mem_dce75000_1_2140:u8)) >> 8:u16)
dsa_R_ESI_32_1_2406:u32 =
  dsa_R_ESI_32_1_2395:u32 +
  (if dsa_R_DF_1_2399:bool == false then 1:u32 else -1:u32) * 2:u32
dsa_R_EDI_32_1_2407:u32 =
  dsa_R_EDI_32_1_2400:u32 +
  (if dsa_R_DF_1_2399:bool == false then 1:u32 else -1:u32) * 2:u32
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf071e, 0, u32, rd
  @context "R_ESI_32" = 0xdce75002, 0, u32, rd
  @context "R_ECX_32" = 0x35, 0, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75002]" = 0x41, 3, u8, rd
  @context "mem32[0xdce75003]" = 0x41, 4, u8, rd
  @context "mem32[0xdce75004]" = 0x41, 5, u8, rd
  @context "mem32[0xdce75005]" = 0x41, 6, u8, rd
  @context "mem32[0xffaf071e]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf071f]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0720]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0721]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0720_1_2408:u8 = low:u8(0:u8)
dsa_mem_ffaf0721_1_2409:u8 = low:u8(0:u8)
dsa_mem_ffaf071f_1_2410:u8 = low:u8(0:u8)
dsa_mem_ffaf071e_1_2411:u8 = low:u8(0:u8)
dsa_R_ZF_1_2412:bool = false
dsa_R_ESI_32_1_2413:u32 = 0xdce75002:u32
dsa_R_AF_1_2414:bool = false
dsa_R_OF_1_2415:bool = false
dsa_R_ECX_32_1_2416:u32 = 0x35:u32
dsa_R_SF_1_2417:bool = false
dsa_R_DF_1_2418:bool = false
dsa_R_EDI_32_1_2419:u32 = 0xffaf071e:u32
dsa_R_CF_1_2420:bool = true
dsa_R_EFLAGS_1_2421:u32 = 0x207:u32
dsa_R_PF_1_2422:bool = true
assert ~(dsa_R_ECX_32_1_2416:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp2"*/
label nocjmp2
dsa_mem_ffaf071e_1_2423:u8 =
  low:u8(pad:u32(dsa_mem_dce75005_1_2145:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75004_1_2144:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75003_1_2143:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75002_1_2142:u8))))
dsa_mem_ffaf071f_1_2424:u8 =
  low:u8((pad:u32(dsa_mem_dce75005_1_2145:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75004_1_2144:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75003_1_2143:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75002_1_2142:u8)))) >> 8:u32)
dsa_mem_ffaf0720_1_2425:u8 =
  low:u8((pad:u32(dsa_mem_dce75005_1_2145:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75004_1_2144:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75003_1_2143:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75002_1_2142:u8)))) >> 0x10:u32)
dsa_mem_ffaf0721_1_2426:u8 =
  low:u8((pad:u32(dsa_mem_dce75005_1_2145:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75004_1_2144:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75003_1_2143:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75002_1_2142:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2427:u32 =
  dsa_R_ESI_32_1_2413:u32 +
  (if dsa_R_DF_1_2418:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2428:u32 =
  dsa_R_EDI_32_1_2419:u32 +
  (if dsa_R_DF_1_2418:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2429:u32 = dsa_R_ECX_32_1_2416:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2429:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp1"*/
label nocjmp1
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0722, 0, u32, rd
  @context "R_ESI_32" = 0xdce75006, 0, u32, rd
  @context "R_ECX_32" = 0x34, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75006]" = 0x41, 7, u8, rd
  @context "mem32[0xdce75007]" = 0x41, 8, u8, rd
  @context "mem32[0xdce75008]" = 0x41, 9, u8, rd
  @context "mem32[0xdce75009]" = 0x41, 10, u8, rd
  @context "mem32[0xffaf0722]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0723]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0724]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0725]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0722_1_2430:u8 = low:u8(0:u8)
dsa_mem_ffaf0725_1_2431:u8 = low:u8(0:u8)
dsa_mem_ffaf0723_1_2432:u8 = low:u8(0:u8)
dsa_mem_ffaf0724_1_2433:u8 = low:u8(0:u8)
dsa_R_ZF_1_2434:bool = false
dsa_R_ESI_32_1_2435:u32 = 0xdce75006:u32
dsa_R_AF_1_2436:bool = false
dsa_R_OF_1_2437:bool = false
dsa_R_SF_1_2438:bool = false
dsa_R_DF_1_2439:bool = false
dsa_R_EDI_32_1_2440:u32 = 0xffaf0722:u32
dsa_R_CF_1_2441:bool = true
dsa_R_EFLAGS_1_2442:u32 = 0x207:u32
dsa_R_PF_1_2443:bool = true
assert ~(dsa_R_ECX_32_1_2429:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp4"*/
label nocjmp4
dsa_mem_ffaf0722_1_2444:u8 =
  low:u8(pad:u32(dsa_mem_dce75009_1_2149:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75008_1_2148:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75007_1_2147:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75006_1_2146:u8))))
dsa_mem_ffaf0723_1_2445:u8 =
  low:u8((pad:u32(dsa_mem_dce75009_1_2149:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75008_1_2148:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75007_1_2147:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75006_1_2146:u8)))) >> 8:u32)
dsa_mem_ffaf0724_1_2446:u8 =
  low:u8((pad:u32(dsa_mem_dce75009_1_2149:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75008_1_2148:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75007_1_2147:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75006_1_2146:u8)))) >> 0x10:u32)
dsa_mem_ffaf0725_1_2447:u8 =
  low:u8((pad:u32(dsa_mem_dce75009_1_2149:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75008_1_2148:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75007_1_2147:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75006_1_2146:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2448:u32 =
  dsa_R_ESI_32_1_2435:u32 +
  (if dsa_R_DF_1_2439:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2449:u32 =
  dsa_R_EDI_32_1_2440:u32 +
  (if dsa_R_DF_1_2439:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2450:u32 = dsa_R_ECX_32_1_2429:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2450:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp3"*/
label nocjmp3
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0726, 0, u32, rd
  @context "R_ESI_32" = 0xdce7500a, 0, u32, rd
  @context "R_ECX_32" = 0x33, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7500a]" = 0x41, 11, u8, rd
  @context "mem32[0xdce7500b]" = 0x41, 12, u8, rd
  @context "mem32[0xdce7500c]" = 0x41, 13, u8, rd
  @context "mem32[0xdce7500d]" = 0x41, 14, u8, rd
  @context "mem32[0xffaf0726]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0727]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0728]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0729]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0727_1_2451:u8 = low:u8(0:u8)
dsa_mem_ffaf0728_1_2452:u8 = low:u8(0:u8)
dsa_mem_ffaf0726_1_2453:u8 = low:u8(0:u8)
dsa_mem_ffaf0729_1_2454:u8 = low:u8(0:u8)
dsa_R_ZF_1_2455:bool = false
dsa_R_ESI_32_1_2456:u32 = 0xdce7500a:u32
dsa_R_AF_1_2457:bool = false
dsa_R_OF_1_2458:bool = false
dsa_R_SF_1_2459:bool = false
dsa_R_DF_1_2460:bool = false
dsa_R_EDI_32_1_2461:u32 = 0xffaf0726:u32
dsa_R_CF_1_2462:bool = true
dsa_R_EFLAGS_1_2463:u32 = 0x207:u32
dsa_R_PF_1_2464:bool = true
assert ~(dsa_R_ECX_32_1_2450:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp6"*/
label nocjmp6
dsa_mem_ffaf0726_1_2465:u8 =
  low:u8(pad:u32(dsa_mem_dce7500d_1_2153:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7500c_1_2152:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7500b_1_2151:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7500a_1_2150:u8))))
dsa_mem_ffaf0727_1_2466:u8 =
  low:u8((pad:u32(dsa_mem_dce7500d_1_2153:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7500c_1_2152:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7500b_1_2151:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7500a_1_2150:u8)))) >> 8:u32)
dsa_mem_ffaf0728_1_2467:u8 =
  low:u8((pad:u32(dsa_mem_dce7500d_1_2153:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7500c_1_2152:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7500b_1_2151:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7500a_1_2150:u8)))) >> 0x10:u32)
dsa_mem_ffaf0729_1_2468:u8 =
  low:u8((pad:u32(dsa_mem_dce7500d_1_2153:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7500c_1_2152:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7500b_1_2151:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7500a_1_2150:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2469:u32 =
  dsa_R_ESI_32_1_2456:u32 +
  (if dsa_R_DF_1_2460:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2470:u32 =
  dsa_R_EDI_32_1_2461:u32 +
  (if dsa_R_DF_1_2460:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2471:u32 = dsa_R_ECX_32_1_2450:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2471:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp5"*/
label nocjmp5
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf072a, 0, u32, rd
  @context "R_ESI_32" = 0xdce7500e, 0, u32, rd
  @context "R_ECX_32" = 0x32, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7500e]" = 0x41, 15, u8, rd
  @context "mem32[0xdce7500f]" = 0x41, 16, u8, rd
  @context "mem32[0xdce75010]" = 0x41, 17, u8, rd
  @context "mem32[0xdce75011]" = 0x41, 18, u8, rd
  @context "mem32[0xffaf072a]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf072b]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf072c]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf072d]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf072a_1_2472:u8 = low:u8(0:u8)
dsa_mem_ffaf072c_1_2473:u8 = low:u8(0:u8)
dsa_mem_ffaf072b_1_2474:u8 = low:u8(0:u8)
dsa_mem_ffaf072d_1_2475:u8 = low:u8(0:u8)
dsa_R_ZF_1_2476:bool = false
dsa_R_ESI_32_1_2477:u32 = 0xdce7500e:u32
dsa_R_AF_1_2478:bool = false
dsa_R_OF_1_2479:bool = false
dsa_R_SF_1_2480:bool = false
dsa_R_DF_1_2481:bool = false
dsa_R_EDI_32_1_2482:u32 = 0xffaf072a:u32
dsa_R_CF_1_2483:bool = true
dsa_R_EFLAGS_1_2484:u32 = 0x207:u32
dsa_R_PF_1_2485:bool = true
assert ~(dsa_R_ECX_32_1_2471:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp8"*/
label nocjmp8
dsa_mem_ffaf072a_1_2486:u8 =
  low:u8(pad:u32(dsa_mem_dce75011_1_2157:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75010_1_2156:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7500f_1_2155:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7500e_1_2154:u8))))
dsa_mem_ffaf072b_1_2487:u8 =
  low:u8((pad:u32(dsa_mem_dce75011_1_2157:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75010_1_2156:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7500f_1_2155:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7500e_1_2154:u8)))) >> 8:u32)
dsa_mem_ffaf072c_1_2488:u8 =
  low:u8((pad:u32(dsa_mem_dce75011_1_2157:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75010_1_2156:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7500f_1_2155:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7500e_1_2154:u8)))) >> 0x10:u32)
dsa_mem_ffaf072d_1_2489:u8 =
  low:u8((pad:u32(dsa_mem_dce75011_1_2157:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75010_1_2156:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7500f_1_2155:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7500e_1_2154:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2490:u32 =
  dsa_R_ESI_32_1_2477:u32 +
  (if dsa_R_DF_1_2481:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2491:u32 =
  dsa_R_EDI_32_1_2482:u32 +
  (if dsa_R_DF_1_2481:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2492:u32 = dsa_R_ECX_32_1_2471:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2492:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp7"*/
label nocjmp7
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf072e, 0, u32, rd
  @context "R_ESI_32" = 0xdce75012, 0, u32, rd
  @context "R_ECX_32" = 0x31, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75012]" = 0x41, 19, u8, rd
  @context "mem32[0xdce75013]" = 0x41, 20, u8, rd
  @context "mem32[0xdce75014]" = 0x41, 21, u8, rd
  @context "mem32[0xdce75015]" = 0x41, 22, u8, rd
  @context "mem32[0xffaf072e]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf072f]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0730]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0731]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0730_1_2493:u8 = low:u8(0:u8)
dsa_mem_ffaf072f_1_2494:u8 = low:u8(0:u8)
dsa_mem_ffaf072e_1_2495:u8 = low:u8(0:u8)
dsa_mem_ffaf0731_1_2496:u8 = low:u8(0:u8)
dsa_R_ZF_1_2497:bool = false
dsa_R_ESI_32_1_2498:u32 = 0xdce75012:u32
dsa_R_AF_1_2499:bool = false
dsa_R_OF_1_2500:bool = false
dsa_R_SF_1_2501:bool = false
dsa_R_DF_1_2502:bool = false
dsa_R_EDI_32_1_2503:u32 = 0xffaf072e:u32
dsa_R_CF_1_2504:bool = true
dsa_R_EFLAGS_1_2505:u32 = 0x207:u32
dsa_R_PF_1_2506:bool = true
assert ~(dsa_R_ECX_32_1_2492:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp10"*/
label nocjmp10
dsa_mem_ffaf072e_1_2507:u8 =
  low:u8(pad:u32(dsa_mem_dce75015_1_2161:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75014_1_2160:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75013_1_2159:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75012_1_2158:u8))))
dsa_mem_ffaf072f_1_2508:u8 =
  low:u8((pad:u32(dsa_mem_dce75015_1_2161:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75014_1_2160:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75013_1_2159:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75012_1_2158:u8)))) >> 8:u32)
dsa_mem_ffaf0730_1_2509:u8 =
  low:u8((pad:u32(dsa_mem_dce75015_1_2161:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75014_1_2160:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75013_1_2159:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75012_1_2158:u8)))) >> 0x10:u32)
dsa_mem_ffaf0731_1_2510:u8 =
  low:u8((pad:u32(dsa_mem_dce75015_1_2161:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75014_1_2160:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75013_1_2159:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75012_1_2158:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2511:u32 =
  dsa_R_ESI_32_1_2498:u32 +
  (if dsa_R_DF_1_2502:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2512:u32 =
  dsa_R_EDI_32_1_2503:u32 +
  (if dsa_R_DF_1_2502:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2513:u32 = dsa_R_ECX_32_1_2492:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2513:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp9"*/
label nocjmp9
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0732, 0, u32, rd
  @context "R_ESI_32" = 0xdce75016, 0, u32, rd
  @context "R_ECX_32" = 0x30, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75016]" = 0x41, 23, u8, rd
  @context "mem32[0xdce75017]" = 0x41, 24, u8, rd
  @context "mem32[0xdce75018]" = 0x41, 25, u8, rd
  @context "mem32[0xdce75019]" = 0x41, 26, u8, rd
  @context "mem32[0xffaf0732]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0733]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0734]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0735]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0734_1_2514:u8 = low:u8(0:u8)
dsa_mem_ffaf0735_1_2515:u8 = low:u8(0:u8)
dsa_mem_ffaf0732_1_2516:u8 = low:u8(0:u8)
dsa_mem_ffaf0733_1_2517:u8 = low:u8(0:u8)
dsa_R_ZF_1_2518:bool = false
dsa_R_ESI_32_1_2519:u32 = 0xdce75016:u32
dsa_R_AF_1_2520:bool = false
dsa_R_OF_1_2521:bool = false
dsa_R_SF_1_2522:bool = false
dsa_R_DF_1_2523:bool = false
dsa_R_EDI_32_1_2524:u32 = 0xffaf0732:u32
dsa_R_CF_1_2525:bool = true
dsa_R_EFLAGS_1_2526:u32 = 0x207:u32
dsa_R_PF_1_2527:bool = true
assert ~(dsa_R_ECX_32_1_2513:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp12"*/
label nocjmp12
dsa_mem_ffaf0732_1_2528:u8 =
  low:u8(pad:u32(dsa_mem_dce75019_1_2165:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75018_1_2164:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75017_1_2163:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75016_1_2162:u8))))
dsa_mem_ffaf0733_1_2529:u8 =
  low:u8((pad:u32(dsa_mem_dce75019_1_2165:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75018_1_2164:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75017_1_2163:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75016_1_2162:u8)))) >> 8:u32)
dsa_mem_ffaf0734_1_2530:u8 =
  low:u8((pad:u32(dsa_mem_dce75019_1_2165:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75018_1_2164:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75017_1_2163:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75016_1_2162:u8)))) >> 0x10:u32)
dsa_mem_ffaf0735_1_2531:u8 =
  low:u8((pad:u32(dsa_mem_dce75019_1_2165:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75018_1_2164:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75017_1_2163:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75016_1_2162:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2532:u32 =
  dsa_R_ESI_32_1_2519:u32 +
  (if dsa_R_DF_1_2523:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2533:u32 =
  dsa_R_EDI_32_1_2524:u32 +
  (if dsa_R_DF_1_2523:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2534:u32 = dsa_R_ECX_32_1_2513:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2534:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp11"*/
label nocjmp11
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0736, 0, u32, rd
  @context "R_ESI_32" = 0xdce7501a, 0, u32, rd
  @context "R_ECX_32" = 0x2f, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7501a]" = 0x41, 27, u8, rd
  @context "mem32[0xdce7501b]" = 0x41, 28, u8, rd
  @context "mem32[0xdce7501c]" = 0x41, 29, u8, rd
  @context "mem32[0xdce7501d]" = 0x41, 30, u8, rd
  @context "mem32[0xffaf0736]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0737]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0738]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0739]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0738_1_2535:u8 = low:u8(0:u8)
dsa_mem_ffaf0736_1_2536:u8 = low:u8(0:u8)
dsa_mem_ffaf0737_1_2537:u8 = low:u8(0:u8)
dsa_mem_ffaf0739_1_2538:u8 = low:u8(0:u8)
dsa_R_ZF_1_2539:bool = false
dsa_R_ESI_32_1_2540:u32 = 0xdce7501a:u32
dsa_R_AF_1_2541:bool = false
dsa_R_OF_1_2542:bool = false
dsa_R_SF_1_2543:bool = false
dsa_R_DF_1_2544:bool = false
dsa_R_EDI_32_1_2545:u32 = 0xffaf0736:u32
dsa_R_CF_1_2546:bool = true
dsa_R_EFLAGS_1_2547:u32 = 0x207:u32
dsa_R_PF_1_2548:bool = true
assert ~(dsa_R_ECX_32_1_2534:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp14"*/
label nocjmp14
dsa_mem_ffaf0736_1_2549:u8 =
  low:u8(pad:u32(dsa_mem_dce7501d_1_2169:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7501c_1_2168:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7501b_1_2167:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7501a_1_2166:u8))))
dsa_mem_ffaf0737_1_2550:u8 =
  low:u8((pad:u32(dsa_mem_dce7501d_1_2169:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7501c_1_2168:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7501b_1_2167:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7501a_1_2166:u8)))) >> 8:u32)
dsa_mem_ffaf0738_1_2551:u8 =
  low:u8((pad:u32(dsa_mem_dce7501d_1_2169:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7501c_1_2168:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7501b_1_2167:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7501a_1_2166:u8)))) >> 0x10:u32)
dsa_mem_ffaf0739_1_2552:u8 =
  low:u8((pad:u32(dsa_mem_dce7501d_1_2169:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7501c_1_2168:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7501b_1_2167:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7501a_1_2166:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2553:u32 =
  dsa_R_ESI_32_1_2540:u32 +
  (if dsa_R_DF_1_2544:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2554:u32 =
  dsa_R_EDI_32_1_2545:u32 +
  (if dsa_R_DF_1_2544:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2555:u32 = dsa_R_ECX_32_1_2534:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2555:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp13"*/
label nocjmp13
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf073a, 0, u32, rd
  @context "R_ESI_32" = 0xdce7501e, 0, u32, rd
  @context "R_ECX_32" = 0x2e, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7501e]" = 0x41, 31, u8, rd
  @context "mem32[0xdce7501f]" = 0x41, 32, u8, rd
  @context "mem32[0xdce75020]" = 0x41, 33, u8, rd
  @context "mem32[0xdce75021]" = 0x41, 34, u8, rd
  @context "mem32[0xffaf073a]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf073b]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf073c]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf073d]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf073c_1_2556:u8 = low:u8(0:u8)
dsa_mem_ffaf073a_1_2557:u8 = low:u8(0:u8)
dsa_mem_ffaf073b_1_2558:u8 = low:u8(0:u8)
dsa_mem_ffaf073d_1_2559:u8 = low:u8(0:u8)
dsa_R_ZF_1_2560:bool = false
dsa_R_ESI_32_1_2561:u32 = 0xdce7501e:u32
dsa_R_AF_1_2562:bool = false
dsa_R_OF_1_2563:bool = false
dsa_R_SF_1_2564:bool = false
dsa_R_DF_1_2565:bool = false
dsa_R_EDI_32_1_2566:u32 = 0xffaf073a:u32
dsa_R_CF_1_2567:bool = true
dsa_R_EFLAGS_1_2568:u32 = 0x207:u32
dsa_R_PF_1_2569:bool = true
assert ~(dsa_R_ECX_32_1_2555:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp16"*/
label nocjmp16
dsa_mem_ffaf073a_1_2570:u8 =
  low:u8(pad:u32(dsa_mem_dce75021_1_2173:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75020_1_2172:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7501f_1_2171:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7501e_1_2170:u8))))
dsa_mem_ffaf073b_1_2571:u8 =
  low:u8((pad:u32(dsa_mem_dce75021_1_2173:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75020_1_2172:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7501f_1_2171:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7501e_1_2170:u8)))) >> 8:u32)
dsa_mem_ffaf073c_1_2572:u8 =
  low:u8((pad:u32(dsa_mem_dce75021_1_2173:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75020_1_2172:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7501f_1_2171:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7501e_1_2170:u8)))) >> 0x10:u32)
dsa_mem_ffaf073d_1_2573:u8 =
  low:u8((pad:u32(dsa_mem_dce75021_1_2173:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75020_1_2172:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7501f_1_2171:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7501e_1_2170:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2574:u32 =
  dsa_R_ESI_32_1_2561:u32 +
  (if dsa_R_DF_1_2565:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2575:u32 =
  dsa_R_EDI_32_1_2566:u32 +
  (if dsa_R_DF_1_2565:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2576:u32 = dsa_R_ECX_32_1_2555:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2576:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp15"*/
label nocjmp15
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf073e, 0, u32, rd
  @context "R_ESI_32" = 0xdce75022, 0, u32, rd
  @context "R_ECX_32" = 0x2d, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75022]" = 0x41, 35, u8, rd
  @context "mem32[0xdce75023]" = 0x41, 36, u8, rd
  @context "mem32[0xdce75024]" = 0x41, 37, u8, rd
  @context "mem32[0xdce75025]" = 0x41, 38, u8, rd
  @context "mem32[0xffaf073e]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf073f]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0740]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0741]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf073f_1_2577:u8 = low:u8(0:u8)
dsa_mem_ffaf0741_1_2578:u8 = low:u8(0:u8)
dsa_mem_ffaf073e_1_2579:u8 = low:u8(0:u8)
dsa_mem_ffaf0740_1_2580:u8 = low:u8(0:u8)
dsa_R_ZF_1_2581:bool = false
dsa_R_ESI_32_1_2582:u32 = 0xdce75022:u32
dsa_R_AF_1_2583:bool = false
dsa_R_OF_1_2584:bool = false
dsa_R_SF_1_2585:bool = false
dsa_R_DF_1_2586:bool = false
dsa_R_EDI_32_1_2587:u32 = 0xffaf073e:u32
dsa_R_CF_1_2588:bool = true
dsa_R_EFLAGS_1_2589:u32 = 0x207:u32
dsa_R_PF_1_2590:bool = true
assert ~(dsa_R_ECX_32_1_2576:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp18"*/
label nocjmp18
dsa_mem_ffaf073e_1_2591:u8 =
  low:u8(pad:u32(dsa_mem_dce75025_1_2177:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75024_1_2176:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75023_1_2175:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75022_1_2174:u8))))
dsa_mem_ffaf073f_1_2592:u8 =
  low:u8((pad:u32(dsa_mem_dce75025_1_2177:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75024_1_2176:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75023_1_2175:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75022_1_2174:u8)))) >> 8:u32)
dsa_mem_ffaf0740_1_2593:u8 =
  low:u8((pad:u32(dsa_mem_dce75025_1_2177:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75024_1_2176:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75023_1_2175:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75022_1_2174:u8)))) >> 0x10:u32)
dsa_mem_ffaf0741_1_2594:u8 =
  low:u8((pad:u32(dsa_mem_dce75025_1_2177:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75024_1_2176:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75023_1_2175:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75022_1_2174:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2595:u32 =
  dsa_R_ESI_32_1_2582:u32 +
  (if dsa_R_DF_1_2586:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2596:u32 =
  dsa_R_EDI_32_1_2587:u32 +
  (if dsa_R_DF_1_2586:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2597:u32 = dsa_R_ECX_32_1_2576:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2597:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp17"*/
label nocjmp17
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0742, 0, u32, rd
  @context "R_ESI_32" = 0xdce75026, 0, u32, rd
  @context "R_ECX_32" = 0x2c, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75026]" = 0x41, 39, u8, rd
  @context "mem32[0xdce75027]" = 0x41, 40, u8, rd
  @context "mem32[0xdce75028]" = 0x41, 41, u8, rd
  @context "mem32[0xdce75029]" = 0x41, 42, u8, rd
  @context "mem32[0xffaf0742]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0743]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0744]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0745]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0742_1_2598:u8 = low:u8(0:u8)
dsa_mem_ffaf0743_1_2599:u8 = low:u8(0:u8)
dsa_mem_ffaf0745_1_2600:u8 = low:u8(0:u8)
dsa_mem_ffaf0744_1_2601:u8 = low:u8(0:u8)
dsa_R_ZF_1_2602:bool = false
dsa_R_ESI_32_1_2603:u32 = 0xdce75026:u32
dsa_R_AF_1_2604:bool = false
dsa_R_OF_1_2605:bool = false
dsa_R_SF_1_2606:bool = false
dsa_R_DF_1_2607:bool = false
dsa_R_EDI_32_1_2608:u32 = 0xffaf0742:u32
dsa_R_CF_1_2609:bool = true
dsa_R_EFLAGS_1_2610:u32 = 0x207:u32
dsa_R_PF_1_2611:bool = true
assert ~(dsa_R_ECX_32_1_2597:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp20"*/
label nocjmp20
dsa_mem_ffaf0742_1_2612:u8 =
  low:u8(pad:u32(dsa_mem_dce75029_1_2181:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75028_1_2180:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75027_1_2179:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75026_1_2178:u8))))
dsa_mem_ffaf0743_1_2613:u8 =
  low:u8((pad:u32(dsa_mem_dce75029_1_2181:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75028_1_2180:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75027_1_2179:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75026_1_2178:u8)))) >> 8:u32)
dsa_mem_ffaf0744_1_2614:u8 =
  low:u8((pad:u32(dsa_mem_dce75029_1_2181:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75028_1_2180:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75027_1_2179:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75026_1_2178:u8)))) >> 0x10:u32)
dsa_mem_ffaf0745_1_2615:u8 =
  low:u8((pad:u32(dsa_mem_dce75029_1_2181:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75028_1_2180:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75027_1_2179:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75026_1_2178:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2616:u32 =
  dsa_R_ESI_32_1_2603:u32 +
  (if dsa_R_DF_1_2607:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2617:u32 =
  dsa_R_EDI_32_1_2608:u32 +
  (if dsa_R_DF_1_2607:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2618:u32 = dsa_R_ECX_32_1_2597:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2618:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp19"*/
label nocjmp19
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0746, 0, u32, rd
  @context "R_ESI_32" = 0xdce7502a, 0, u32, rd
  @context "R_ECX_32" = 0x2b, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7502a]" = 0x41, 43, u8, rd
  @context "mem32[0xdce7502b]" = 0x41, 44, u8, rd
  @context "mem32[0xdce7502c]" = 0x41, 45, u8, rd
  @context "mem32[0xdce7502d]" = 0x41, 46, u8, rd
  @context "mem32[0xffaf0746]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0747]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0748]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0749]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0746_1_2619:u8 = low:u8(0:u8)
dsa_mem_ffaf0747_1_2620:u8 = low:u8(0:u8)
dsa_mem_ffaf0748_1_2621:u8 = low:u8(0:u8)
dsa_mem_ffaf0749_1_2622:u8 = low:u8(0:u8)
dsa_R_ZF_1_2623:bool = false
dsa_R_ESI_32_1_2624:u32 = 0xdce7502a:u32
dsa_R_AF_1_2625:bool = false
dsa_R_OF_1_2626:bool = false
dsa_R_SF_1_2627:bool = false
dsa_R_DF_1_2628:bool = false
dsa_R_EDI_32_1_2629:u32 = 0xffaf0746:u32
dsa_R_CF_1_2630:bool = true
dsa_R_EFLAGS_1_2631:u32 = 0x207:u32
dsa_R_PF_1_2632:bool = true
assert ~(dsa_R_ECX_32_1_2618:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp22"*/
label nocjmp22
dsa_mem_ffaf0746_1_2633:u8 =
  low:u8(pad:u32(dsa_mem_dce7502d_1_2185:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7502c_1_2184:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7502b_1_2183:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7502a_1_2182:u8))))
dsa_mem_ffaf0747_1_2634:u8 =
  low:u8((pad:u32(dsa_mem_dce7502d_1_2185:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7502c_1_2184:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7502b_1_2183:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7502a_1_2182:u8)))) >> 8:u32)
dsa_mem_ffaf0748_1_2635:u8 =
  low:u8((pad:u32(dsa_mem_dce7502d_1_2185:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7502c_1_2184:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7502b_1_2183:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7502a_1_2182:u8)))) >> 0x10:u32)
dsa_mem_ffaf0749_1_2636:u8 =
  low:u8((pad:u32(dsa_mem_dce7502d_1_2185:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7502c_1_2184:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7502b_1_2183:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7502a_1_2182:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2637:u32 =
  dsa_R_ESI_32_1_2624:u32 +
  (if dsa_R_DF_1_2628:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2638:u32 =
  dsa_R_EDI_32_1_2629:u32 +
  (if dsa_R_DF_1_2628:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2639:u32 = dsa_R_ECX_32_1_2618:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2639:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp21"*/
label nocjmp21
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf074a, 0, u32, rd
  @context "R_ESI_32" = 0xdce7502e, 0, u32, rd
  @context "R_ECX_32" = 0x2a, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7502e]" = 0x41, 47, u8, rd
  @context "mem32[0xdce7502f]" = 0x41, 48, u8, rd
  @context "mem32[0xdce75030]" = 0x41, 49, u8, rd
  @context "mem32[0xdce75031]" = 0x41, 50, u8, rd
  @context "mem32[0xffaf074a]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf074b]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf074c]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf074d]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf074b_1_2640:u8 = low:u8(0:u8)
dsa_mem_ffaf074c_1_2641:u8 = low:u8(0:u8)
dsa_mem_ffaf074a_1_2642:u8 = low:u8(0:u8)
dsa_mem_ffaf074d_1_2643:u8 = low:u8(0:u8)
dsa_R_ZF_1_2644:bool = false
dsa_R_ESI_32_1_2645:u32 = 0xdce7502e:u32
dsa_R_AF_1_2646:bool = false
dsa_R_OF_1_2647:bool = false
dsa_R_SF_1_2648:bool = false
dsa_R_DF_1_2649:bool = false
dsa_R_EDI_32_1_2650:u32 = 0xffaf074a:u32
dsa_R_CF_1_2651:bool = true
dsa_R_EFLAGS_1_2652:u32 = 0x207:u32
dsa_R_PF_1_2653:bool = true
assert ~(dsa_R_ECX_32_1_2639:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp24"*/
label nocjmp24
dsa_mem_ffaf074a_1_2654:u8 =
  low:u8(pad:u32(dsa_mem_dce75031_1_2189:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75030_1_2188:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7502f_1_2187:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7502e_1_2186:u8))))
dsa_mem_ffaf074b_1_2655:u8 =
  low:u8((pad:u32(dsa_mem_dce75031_1_2189:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75030_1_2188:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7502f_1_2187:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7502e_1_2186:u8)))) >> 8:u32)
dsa_mem_ffaf074c_1_2656:u8 =
  low:u8((pad:u32(dsa_mem_dce75031_1_2189:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75030_1_2188:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7502f_1_2187:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7502e_1_2186:u8)))) >> 0x10:u32)
dsa_mem_ffaf074d_1_2657:u8 =
  low:u8((pad:u32(dsa_mem_dce75031_1_2189:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75030_1_2188:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7502f_1_2187:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7502e_1_2186:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2658:u32 =
  dsa_R_ESI_32_1_2645:u32 +
  (if dsa_R_DF_1_2649:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2659:u32 =
  dsa_R_EDI_32_1_2650:u32 +
  (if dsa_R_DF_1_2649:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2660:u32 = dsa_R_ECX_32_1_2639:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2660:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp23"*/
label nocjmp23
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf074e, 0, u32, rd
  @context "R_ESI_32" = 0xdce75032, 0, u32, rd
  @context "R_ECX_32" = 0x29, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75032]" = 0x41, 51, u8, rd
  @context "mem32[0xdce75033]" = 0x41, 52, u8, rd
  @context "mem32[0xdce75034]" = 0x41, 53, u8, rd
  @context "mem32[0xdce75035]" = 0x41, 54, u8, rd
  @context "mem32[0xffaf074e]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf074f]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0750]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0751]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf074f_1_2661:u8 = low:u8(0:u8)
dsa_mem_ffaf0751_1_2662:u8 = low:u8(0:u8)
dsa_mem_ffaf074e_1_2663:u8 = low:u8(0:u8)
dsa_mem_ffaf0750_1_2664:u8 = low:u8(0:u8)
dsa_R_ZF_1_2665:bool = false
dsa_R_ESI_32_1_2666:u32 = 0xdce75032:u32
dsa_R_AF_1_2667:bool = false
dsa_R_OF_1_2668:bool = false
dsa_R_SF_1_2669:bool = false
dsa_R_DF_1_2670:bool = false
dsa_R_EDI_32_1_2671:u32 = 0xffaf074e:u32
dsa_R_CF_1_2672:bool = true
dsa_R_EFLAGS_1_2673:u32 = 0x207:u32
dsa_R_PF_1_2674:bool = true
assert ~(dsa_R_ECX_32_1_2660:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp26"*/
label nocjmp26
dsa_mem_ffaf074e_1_2675:u8 =
  low:u8(pad:u32(dsa_mem_dce75035_1_2193:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75034_1_2192:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75033_1_2191:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75032_1_2190:u8))))
dsa_mem_ffaf074f_1_2676:u8 =
  low:u8((pad:u32(dsa_mem_dce75035_1_2193:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75034_1_2192:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75033_1_2191:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75032_1_2190:u8)))) >> 8:u32)
dsa_mem_ffaf0750_1_2677:u8 =
  low:u8((pad:u32(dsa_mem_dce75035_1_2193:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75034_1_2192:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75033_1_2191:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75032_1_2190:u8)))) >> 0x10:u32)
dsa_mem_ffaf0751_1_2678:u8 =
  low:u8((pad:u32(dsa_mem_dce75035_1_2193:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75034_1_2192:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75033_1_2191:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75032_1_2190:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2679:u32 =
  dsa_R_ESI_32_1_2666:u32 +
  (if dsa_R_DF_1_2670:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2680:u32 =
  dsa_R_EDI_32_1_2671:u32 +
  (if dsa_R_DF_1_2670:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2681:u32 = dsa_R_ECX_32_1_2660:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2681:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp25"*/
label nocjmp25
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0752, 0, u32, rd
  @context "R_ESI_32" = 0xdce75036, 0, u32, rd
  @context "R_ECX_32" = 0x28, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75036]" = 0x41, 55, u8, rd
  @context "mem32[0xdce75037]" = 0x41, 56, u8, rd
  @context "mem32[0xdce75038]" = 0x41, 57, u8, rd
  @context "mem32[0xdce75039]" = 0x41, 58, u8, rd
  @context "mem32[0xffaf0752]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0753]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0754]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0755]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0753_1_2682:u8 = low:u8(0:u8)
dsa_mem_ffaf0755_1_2683:u8 = low:u8(0:u8)
dsa_mem_ffaf0752_1_2684:u8 = low:u8(0:u8)
dsa_mem_ffaf0754_1_2685:u8 = low:u8(0:u8)
dsa_R_ZF_1_2686:bool = false
dsa_R_ESI_32_1_2687:u32 = 0xdce75036:u32
dsa_R_AF_1_2688:bool = false
dsa_R_OF_1_2689:bool = false
dsa_R_SF_1_2690:bool = false
dsa_R_DF_1_2691:bool = false
dsa_R_EDI_32_1_2692:u32 = 0xffaf0752:u32
dsa_R_CF_1_2693:bool = true
dsa_R_EFLAGS_1_2694:u32 = 0x207:u32
dsa_R_PF_1_2695:bool = true
assert ~(dsa_R_ECX_32_1_2681:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp28"*/
label nocjmp28
dsa_mem_ffaf0752_1_2696:u8 =
  low:u8(pad:u32(dsa_mem_dce75039_1_2197:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75038_1_2196:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75037_1_2195:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75036_1_2194:u8))))
dsa_mem_ffaf0753_1_2697:u8 =
  low:u8((pad:u32(dsa_mem_dce75039_1_2197:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75038_1_2196:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75037_1_2195:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75036_1_2194:u8)))) >> 8:u32)
dsa_mem_ffaf0754_1_2698:u8 =
  low:u8((pad:u32(dsa_mem_dce75039_1_2197:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75038_1_2196:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75037_1_2195:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75036_1_2194:u8)))) >> 0x10:u32)
dsa_mem_ffaf0755_1_2699:u8 =
  low:u8((pad:u32(dsa_mem_dce75039_1_2197:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75038_1_2196:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75037_1_2195:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75036_1_2194:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2700:u32 =
  dsa_R_ESI_32_1_2687:u32 +
  (if dsa_R_DF_1_2691:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2701:u32 =
  dsa_R_EDI_32_1_2692:u32 +
  (if dsa_R_DF_1_2691:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2702:u32 = dsa_R_ECX_32_1_2681:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2702:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp27"*/
label nocjmp27
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0756, 0, u32, rd
  @context "R_ESI_32" = 0xdce7503a, 0, u32, rd
  @context "R_ECX_32" = 0x27, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7503a]" = 0x41, 59, u8, rd
  @context "mem32[0xdce7503b]" = 0x41, 60, u8, rd
  @context "mem32[0xdce7503c]" = 0x41, 61, u8, rd
  @context "mem32[0xdce7503d]" = 0x41, 62, u8, rd
  @context "mem32[0xffaf0756]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0757]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0758]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0759]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0757_1_2703:u8 = low:u8(0:u8)
dsa_mem_ffaf0756_1_2704:u8 = low:u8(0:u8)
dsa_mem_ffaf0758_1_2705:u8 = low:u8(0:u8)
dsa_mem_ffaf0759_1_2706:u8 = low:u8(0:u8)
dsa_R_ZF_1_2707:bool = false
dsa_R_ESI_32_1_2708:u32 = 0xdce7503a:u32
dsa_R_AF_1_2709:bool = false
dsa_R_OF_1_2710:bool = false
dsa_R_SF_1_2711:bool = false
dsa_R_DF_1_2712:bool = false
dsa_R_EDI_32_1_2713:u32 = 0xffaf0756:u32
dsa_R_CF_1_2714:bool = true
dsa_R_EFLAGS_1_2715:u32 = 0x207:u32
dsa_R_PF_1_2716:bool = true
assert ~(dsa_R_ECX_32_1_2702:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp30"*/
label nocjmp30
dsa_mem_ffaf0756_1_2717:u8 =
  low:u8(pad:u32(dsa_mem_dce7503d_1_2201:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7503c_1_2200:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7503b_1_2199:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7503a_1_2198:u8))))
dsa_mem_ffaf0757_1_2718:u8 =
  low:u8((pad:u32(dsa_mem_dce7503d_1_2201:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7503c_1_2200:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7503b_1_2199:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7503a_1_2198:u8)))) >> 8:u32)
dsa_mem_ffaf0758_1_2719:u8 =
  low:u8((pad:u32(dsa_mem_dce7503d_1_2201:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7503c_1_2200:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7503b_1_2199:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7503a_1_2198:u8)))) >> 0x10:u32)
dsa_mem_ffaf0759_1_2720:u8 =
  low:u8((pad:u32(dsa_mem_dce7503d_1_2201:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7503c_1_2200:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7503b_1_2199:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7503a_1_2198:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2721:u32 =
  dsa_R_ESI_32_1_2708:u32 +
  (if dsa_R_DF_1_2712:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2722:u32 =
  dsa_R_EDI_32_1_2713:u32 +
  (if dsa_R_DF_1_2712:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2723:u32 = dsa_R_ECX_32_1_2702:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2723:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp29"*/
label nocjmp29
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf075a, 0, u32, rd
  @context "R_ESI_32" = 0xdce7503e, 0, u32, rd
  @context "R_ECX_32" = 0x26, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7503e]" = 0x41, 63, u8, rd
  @context "mem32[0xdce7503f]" = 0x41, 64, u8, rd
  @context "mem32[0xdce75040]" = 0x41, 65, u8, rd
  @context "mem32[0xdce75041]" = 0x41, 66, u8, rd
  @context "mem32[0xffaf075a]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf075b]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf075c]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf075d]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf075d_1_2724:u8 = low:u8(0:u8)
dsa_mem_ffaf075a_1_2725:u8 = low:u8(0:u8)
dsa_mem_ffaf075c_1_2726:u8 = low:u8(0:u8)
dsa_mem_ffaf075b_1_2727:u8 = low:u8(0:u8)
dsa_R_ZF_1_2728:bool = false
dsa_R_ESI_32_1_2729:u32 = 0xdce7503e:u32
dsa_R_AF_1_2730:bool = false
dsa_R_OF_1_2731:bool = false
dsa_R_SF_1_2732:bool = false
dsa_R_DF_1_2733:bool = false
dsa_R_EDI_32_1_2734:u32 = 0xffaf075a:u32
dsa_R_CF_1_2735:bool = true
dsa_R_EFLAGS_1_2736:u32 = 0x207:u32
dsa_R_PF_1_2737:bool = true
assert ~(dsa_R_ECX_32_1_2723:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp32"*/
label nocjmp32
dsa_mem_ffaf075a_1_2738:u8 =
  low:u8(pad:u32(dsa_mem_dce75041_1_2205:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75040_1_2204:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7503f_1_2203:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7503e_1_2202:u8))))
dsa_mem_ffaf075b_1_2739:u8 =
  low:u8((pad:u32(dsa_mem_dce75041_1_2205:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75040_1_2204:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7503f_1_2203:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7503e_1_2202:u8)))) >> 8:u32)
dsa_mem_ffaf075c_1_2740:u8 =
  low:u8((pad:u32(dsa_mem_dce75041_1_2205:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75040_1_2204:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7503f_1_2203:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7503e_1_2202:u8)))) >> 0x10:u32)
dsa_mem_ffaf075d_1_2741:u8 =
  low:u8((pad:u32(dsa_mem_dce75041_1_2205:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75040_1_2204:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7503f_1_2203:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7503e_1_2202:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2742:u32 =
  dsa_R_ESI_32_1_2729:u32 +
  (if dsa_R_DF_1_2733:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2743:u32 =
  dsa_R_EDI_32_1_2734:u32 +
  (if dsa_R_DF_1_2733:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2744:u32 = dsa_R_ECX_32_1_2723:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2744:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp31"*/
label nocjmp31
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf075e, 0, u32, rd
  @context "R_ESI_32" = 0xdce75042, 0, u32, rd
  @context "R_ECX_32" = 0x25, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75042]" = 0x41, 67, u8, rd
  @context "mem32[0xdce75043]" = 0x41, 68, u8, rd
  @context "mem32[0xdce75044]" = 0x41, 69, u8, rd
  @context "mem32[0xdce75045]" = 0x41, 70, u8, rd
  @context "mem32[0xffaf075e]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf075f]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0760]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0761]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0760_1_2745:u8 = low:u8(0:u8)
dsa_mem_ffaf075e_1_2746:u8 = low:u8(0:u8)
dsa_mem_ffaf0761_1_2747:u8 = low:u8(0:u8)
dsa_mem_ffaf075f_1_2748:u8 = low:u8(0:u8)
dsa_R_ZF_1_2749:bool = false
dsa_R_ESI_32_1_2750:u32 = 0xdce75042:u32
dsa_R_AF_1_2751:bool = false
dsa_R_OF_1_2752:bool = false
dsa_R_SF_1_2753:bool = false
dsa_R_DF_1_2754:bool = false
dsa_R_EDI_32_1_2755:u32 = 0xffaf075e:u32
dsa_R_CF_1_2756:bool = true
dsa_R_EFLAGS_1_2757:u32 = 0x207:u32
dsa_R_PF_1_2758:bool = true
assert ~(dsa_R_ECX_32_1_2744:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp34"*/
label nocjmp34
dsa_mem_ffaf075e_1_2759:u8 =
  low:u8(pad:u32(dsa_mem_dce75045_1_2209:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75044_1_2208:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75043_1_2207:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75042_1_2206:u8))))
dsa_mem_ffaf075f_1_2760:u8 =
  low:u8((pad:u32(dsa_mem_dce75045_1_2209:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75044_1_2208:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75043_1_2207:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75042_1_2206:u8)))) >> 8:u32)
dsa_mem_ffaf0760_1_2761:u8 =
  low:u8((pad:u32(dsa_mem_dce75045_1_2209:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75044_1_2208:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75043_1_2207:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75042_1_2206:u8)))) >> 0x10:u32)
dsa_mem_ffaf0761_1_2762:u8 =
  low:u8((pad:u32(dsa_mem_dce75045_1_2209:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75044_1_2208:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75043_1_2207:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75042_1_2206:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2763:u32 =
  dsa_R_ESI_32_1_2750:u32 +
  (if dsa_R_DF_1_2754:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2764:u32 =
  dsa_R_EDI_32_1_2755:u32 +
  (if dsa_R_DF_1_2754:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2765:u32 = dsa_R_ECX_32_1_2744:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2765:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp33"*/
label nocjmp33
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0762, 0, u32, rd
  @context "R_ESI_32" = 0xdce75046, 0, u32, rd
  @context "R_ECX_32" = 0x24, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75046]" = 0x41, 71, u8, rd
  @context "mem32[0xdce75047]" = 0x41, 72, u8, rd
  @context "mem32[0xdce75048]" = 0x41, 73, u8, rd
  @context "mem32[0xdce75049]" = 0x41, 74, u8, rd
  @context "mem32[0xffaf0762]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0763]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0764]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0765]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0765_1_2766:u8 = low:u8(0:u8)
dsa_mem_ffaf0763_1_2767:u8 = low:u8(0:u8)
dsa_mem_ffaf0764_1_2768:u8 = low:u8(0:u8)
dsa_mem_ffaf0762_1_2769:u8 = low:u8(0:u8)
dsa_R_ZF_1_2770:bool = false
dsa_R_ESI_32_1_2771:u32 = 0xdce75046:u32
dsa_R_AF_1_2772:bool = false
dsa_R_OF_1_2773:bool = false
dsa_R_SF_1_2774:bool = false
dsa_R_DF_1_2775:bool = false
dsa_R_EDI_32_1_2776:u32 = 0xffaf0762:u32
dsa_R_CF_1_2777:bool = true
dsa_R_EFLAGS_1_2778:u32 = 0x207:u32
dsa_R_PF_1_2779:bool = true
assert ~(dsa_R_ECX_32_1_2765:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp36"*/
label nocjmp36
dsa_mem_ffaf0762_1_2780:u8 =
  low:u8(pad:u32(dsa_mem_dce75049_1_2213:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75048_1_2212:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75047_1_2211:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75046_1_2210:u8))))
dsa_mem_ffaf0763_1_2781:u8 =
  low:u8((pad:u32(dsa_mem_dce75049_1_2213:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75048_1_2212:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75047_1_2211:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75046_1_2210:u8)))) >> 8:u32)
dsa_mem_ffaf0764_1_2782:u8 =
  low:u8((pad:u32(dsa_mem_dce75049_1_2213:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75048_1_2212:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75047_1_2211:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75046_1_2210:u8)))) >> 0x10:u32)
dsa_mem_ffaf0765_1_2783:u8 =
  low:u8((pad:u32(dsa_mem_dce75049_1_2213:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75048_1_2212:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75047_1_2211:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75046_1_2210:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2784:u32 =
  dsa_R_ESI_32_1_2771:u32 +
  (if dsa_R_DF_1_2775:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2785:u32 =
  dsa_R_EDI_32_1_2776:u32 +
  (if dsa_R_DF_1_2775:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2786:u32 = dsa_R_ECX_32_1_2765:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2786:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp35"*/
label nocjmp35
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0766, 0, u32, rd
  @context "R_ESI_32" = 0xdce7504a, 0, u32, rd
  @context "R_ECX_32" = 0x23, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7504a]" = 0x41, 75, u8, rd
  @context "mem32[0xdce7504b]" = 0x41, 76, u8, rd
  @context "mem32[0xdce7504c]" = 0x41, 77, u8, rd
  @context "mem32[0xdce7504d]" = 0x41, 78, u8, rd
  @context "mem32[0xffaf0766]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0767]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0768]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0769]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0766_1_2787:u8 = low:u8(0:u8)
dsa_mem_ffaf0767_1_2788:u8 = low:u8(0:u8)
dsa_mem_ffaf0768_1_2789:u8 = low:u8(0:u8)
dsa_mem_ffaf0769_1_2790:u8 = low:u8(0:u8)
dsa_R_ZF_1_2791:bool = false
dsa_R_ESI_32_1_2792:u32 = 0xdce7504a:u32
dsa_R_AF_1_2793:bool = false
dsa_R_OF_1_2794:bool = false
dsa_R_SF_1_2795:bool = false
dsa_R_DF_1_2796:bool = false
dsa_R_EDI_32_1_2797:u32 = 0xffaf0766:u32
dsa_R_CF_1_2798:bool = true
dsa_R_EFLAGS_1_2799:u32 = 0x207:u32
dsa_R_PF_1_2800:bool = true
assert ~(dsa_R_ECX_32_1_2786:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp38"*/
label nocjmp38
dsa_mem_ffaf0766_1_2801:u8 =
  low:u8(pad:u32(dsa_mem_dce7504d_1_2217:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7504c_1_2216:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7504b_1_2215:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7504a_1_2214:u8))))
dsa_mem_ffaf0767_1_2802:u8 =
  low:u8((pad:u32(dsa_mem_dce7504d_1_2217:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7504c_1_2216:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7504b_1_2215:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7504a_1_2214:u8)))) >> 8:u32)
dsa_mem_ffaf0768_1_2803:u8 =
  low:u8((pad:u32(dsa_mem_dce7504d_1_2217:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7504c_1_2216:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7504b_1_2215:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7504a_1_2214:u8)))) >> 0x10:u32)
dsa_mem_ffaf0769_1_2804:u8 =
  low:u8((pad:u32(dsa_mem_dce7504d_1_2217:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7504c_1_2216:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7504b_1_2215:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7504a_1_2214:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2805:u32 =
  dsa_R_ESI_32_1_2792:u32 +
  (if dsa_R_DF_1_2796:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2806:u32 =
  dsa_R_EDI_32_1_2797:u32 +
  (if dsa_R_DF_1_2796:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2807:u32 = dsa_R_ECX_32_1_2786:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2807:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp37"*/
label nocjmp37
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf076a, 0, u32, rd
  @context "R_ESI_32" = 0xdce7504e, 0, u32, rd
  @context "R_ECX_32" = 0x22, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7504e]" = 0x41, 79, u8, rd
  @context "mem32[0xdce7504f]" = 0x41, 80, u8, rd
  @context "mem32[0xdce75050]" = 0x41, 81, u8, rd
  @context "mem32[0xdce75051]" = 0x41, 82, u8, rd
  @context "mem32[0xffaf076a]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf076b]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf076c]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf076d]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf076c_1_2808:u8 = low:u8(0:u8)
dsa_mem_ffaf076a_1_2809:u8 = low:u8(0:u8)
dsa_mem_ffaf076d_1_2810:u8 = low:u8(0:u8)
dsa_mem_ffaf076b_1_2811:u8 = low:u8(0:u8)
dsa_R_ZF_1_2812:bool = false
dsa_R_ESI_32_1_2813:u32 = 0xdce7504e:u32
dsa_R_AF_1_2814:bool = false
dsa_R_OF_1_2815:bool = false
dsa_R_SF_1_2816:bool = false
dsa_R_DF_1_2817:bool = false
dsa_R_EDI_32_1_2818:u32 = 0xffaf076a:u32
dsa_R_CF_1_2819:bool = true
dsa_R_EFLAGS_1_2820:u32 = 0x207:u32
dsa_R_PF_1_2821:bool = true
assert ~(dsa_R_ECX_32_1_2807:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp40"*/
label nocjmp40
dsa_mem_ffaf076a_1_2822:u8 =
  low:u8(pad:u32(dsa_mem_dce75051_1_2221:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75050_1_2220:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7504f_1_2219:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7504e_1_2218:u8))))
dsa_mem_ffaf076b_1_2823:u8 =
  low:u8((pad:u32(dsa_mem_dce75051_1_2221:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75050_1_2220:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7504f_1_2219:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7504e_1_2218:u8)))) >> 8:u32)
dsa_mem_ffaf076c_1_2824:u8 =
  low:u8((pad:u32(dsa_mem_dce75051_1_2221:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75050_1_2220:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7504f_1_2219:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7504e_1_2218:u8)))) >> 0x10:u32)
dsa_mem_ffaf076d_1_2825:u8 =
  low:u8((pad:u32(dsa_mem_dce75051_1_2221:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75050_1_2220:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7504f_1_2219:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7504e_1_2218:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2826:u32 =
  dsa_R_ESI_32_1_2813:u32 +
  (if dsa_R_DF_1_2817:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2827:u32 =
  dsa_R_EDI_32_1_2818:u32 +
  (if dsa_R_DF_1_2817:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2828:u32 = dsa_R_ECX_32_1_2807:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2828:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp39"*/
label nocjmp39
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf076e, 0, u32, rd
  @context "R_ESI_32" = 0xdce75052, 0, u32, rd
  @context "R_ECX_32" = 0x21, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75052]" = 0x41, 83, u8, rd
  @context "mem32[0xdce75053]" = 0x41, 84, u8, rd
  @context "mem32[0xdce75054]" = 0x41, 85, u8, rd
  @context "mem32[0xdce75055]" = 0x41, 86, u8, rd
  @context "mem32[0xffaf076e]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf076f]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0770]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0771]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0771_1_2829:u8 = low:u8(0:u8)
dsa_mem_ffaf076f_1_2830:u8 = low:u8(0:u8)
dsa_mem_ffaf076e_1_2831:u8 = low:u8(0:u8)
dsa_mem_ffaf0770_1_2832:u8 = low:u8(0:u8)
dsa_R_ZF_1_2833:bool = false
dsa_R_ESI_32_1_2834:u32 = 0xdce75052:u32
dsa_R_AF_1_2835:bool = false
dsa_R_OF_1_2836:bool = false
dsa_R_SF_1_2837:bool = false
dsa_R_DF_1_2838:bool = false
dsa_R_EDI_32_1_2839:u32 = 0xffaf076e:u32
dsa_R_CF_1_2840:bool = true
dsa_R_EFLAGS_1_2841:u32 = 0x207:u32
dsa_R_PF_1_2842:bool = true
assert ~(dsa_R_ECX_32_1_2828:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp42"*/
label nocjmp42
dsa_mem_ffaf076e_1_2843:u8 =
  low:u8(pad:u32(dsa_mem_dce75055_1_2225:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75054_1_2224:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75053_1_2223:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75052_1_2222:u8))))
dsa_mem_ffaf076f_1_2844:u8 =
  low:u8((pad:u32(dsa_mem_dce75055_1_2225:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75054_1_2224:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75053_1_2223:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75052_1_2222:u8)))) >> 8:u32)
dsa_mem_ffaf0770_1_2845:u8 =
  low:u8((pad:u32(dsa_mem_dce75055_1_2225:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75054_1_2224:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75053_1_2223:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75052_1_2222:u8)))) >> 0x10:u32)
dsa_mem_ffaf0771_1_2846:u8 =
  low:u8((pad:u32(dsa_mem_dce75055_1_2225:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75054_1_2224:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75053_1_2223:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75052_1_2222:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2847:u32 =
  dsa_R_ESI_32_1_2834:u32 +
  (if dsa_R_DF_1_2838:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2848:u32 =
  dsa_R_EDI_32_1_2839:u32 +
  (if dsa_R_DF_1_2838:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2849:u32 = dsa_R_ECX_32_1_2828:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2849:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp41"*/
label nocjmp41
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0772, 0, u32, rd
  @context "R_ESI_32" = 0xdce75056, 0, u32, rd
  @context "R_ECX_32" = 0x20, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75056]" = 0x41, 87, u8, rd
  @context "mem32[0xdce75057]" = 0x41, 88, u8, rd
  @context "mem32[0xdce75058]" = 0x41, 89, u8, rd
  @context "mem32[0xdce75059]" = 0x41, 90, u8, rd
  @context "mem32[0xffaf0772]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0773]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0774]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0775]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0774_1_2850:u8 = low:u8(0:u8)
dsa_mem_ffaf0773_1_2851:u8 = low:u8(0:u8)
dsa_mem_ffaf0775_1_2852:u8 = low:u8(0:u8)
dsa_mem_ffaf0772_1_2853:u8 = low:u8(0:u8)
dsa_R_ZF_1_2854:bool = false
dsa_R_ESI_32_1_2855:u32 = 0xdce75056:u32
dsa_R_AF_1_2856:bool = false
dsa_R_OF_1_2857:bool = false
dsa_R_SF_1_2858:bool = false
dsa_R_DF_1_2859:bool = false
dsa_R_EDI_32_1_2860:u32 = 0xffaf0772:u32
dsa_R_CF_1_2861:bool = true
dsa_R_EFLAGS_1_2862:u32 = 0x207:u32
dsa_R_PF_1_2863:bool = true
assert ~(dsa_R_ECX_32_1_2849:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp44"*/
label nocjmp44
dsa_mem_ffaf0772_1_2864:u8 =
  low:u8(pad:u32(dsa_mem_dce75059_1_2229:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75058_1_2228:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75057_1_2227:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75056_1_2226:u8))))
dsa_mem_ffaf0773_1_2865:u8 =
  low:u8((pad:u32(dsa_mem_dce75059_1_2229:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75058_1_2228:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75057_1_2227:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75056_1_2226:u8)))) >> 8:u32)
dsa_mem_ffaf0774_1_2866:u8 =
  low:u8((pad:u32(dsa_mem_dce75059_1_2229:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75058_1_2228:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75057_1_2227:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75056_1_2226:u8)))) >> 0x10:u32)
dsa_mem_ffaf0775_1_2867:u8 =
  low:u8((pad:u32(dsa_mem_dce75059_1_2229:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75058_1_2228:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75057_1_2227:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75056_1_2226:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2868:u32 =
  dsa_R_ESI_32_1_2855:u32 +
  (if dsa_R_DF_1_2859:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2869:u32 =
  dsa_R_EDI_32_1_2860:u32 +
  (if dsa_R_DF_1_2859:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2870:u32 = dsa_R_ECX_32_1_2849:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2870:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp43"*/
label nocjmp43
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0776, 0, u32, rd
  @context "R_ESI_32" = 0xdce7505a, 0, u32, rd
  @context "R_ECX_32" = 0x1f, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7505a]" = 0x41, 91, u8, rd
  @context "mem32[0xdce7505b]" = 0x41, 92, u8, rd
  @context "mem32[0xdce7505c]" = 0x41, 93, u8, rd
  @context "mem32[0xdce7505d]" = 0x41, 94, u8, rd
  @context "mem32[0xffaf0776]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0777]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0778]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0779]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0779_1_2871:u8 = low:u8(0:u8)
dsa_mem_ffaf0778_1_2872:u8 = low:u8(0:u8)
dsa_mem_ffaf0777_1_2873:u8 = low:u8(0:u8)
dsa_mem_ffaf0776_1_2874:u8 = low:u8(0:u8)
dsa_R_ZF_1_2875:bool = false
dsa_R_ESI_32_1_2876:u32 = 0xdce7505a:u32
dsa_R_AF_1_2877:bool = false
dsa_R_OF_1_2878:bool = false
dsa_R_SF_1_2879:bool = false
dsa_R_DF_1_2880:bool = false
dsa_R_EDI_32_1_2881:u32 = 0xffaf0776:u32
dsa_R_CF_1_2882:bool = true
dsa_R_EFLAGS_1_2883:u32 = 0x207:u32
dsa_R_PF_1_2884:bool = true
assert ~(dsa_R_ECX_32_1_2870:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp46"*/
label nocjmp46
dsa_mem_ffaf0776_1_2885:u8 =
  low:u8(pad:u32(dsa_mem_dce7505d_1_2233:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7505c_1_2232:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7505b_1_2231:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7505a_1_2230:u8))))
dsa_mem_ffaf0777_1_2886:u8 =
  low:u8((pad:u32(dsa_mem_dce7505d_1_2233:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7505c_1_2232:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7505b_1_2231:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7505a_1_2230:u8)))) >> 8:u32)
dsa_mem_ffaf0778_1_2887:u8 =
  low:u8((pad:u32(dsa_mem_dce7505d_1_2233:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7505c_1_2232:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7505b_1_2231:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7505a_1_2230:u8)))) >> 0x10:u32)
dsa_mem_ffaf0779_1_2888:u8 =
  low:u8((pad:u32(dsa_mem_dce7505d_1_2233:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7505c_1_2232:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7505b_1_2231:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7505a_1_2230:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2889:u32 =
  dsa_R_ESI_32_1_2876:u32 +
  (if dsa_R_DF_1_2880:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2890:u32 =
  dsa_R_EDI_32_1_2881:u32 +
  (if dsa_R_DF_1_2880:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2891:u32 = dsa_R_ECX_32_1_2870:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2891:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp45"*/
label nocjmp45
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf077a, 0, u32, rd
  @context "R_ESI_32" = 0xdce7505e, 0, u32, rd
  @context "R_ECX_32" = 0x1e, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7505e]" = 0x41, 95, u8, rd
  @context "mem32[0xdce7505f]" = 0x41, 96, u8, rd
  @context "mem32[0xdce75060]" = 0x41, 97, u8, rd
  @context "mem32[0xdce75061]" = 0x41, 98, u8, rd
  @context "mem32[0xffaf077a]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf077b]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf077c]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf077d]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf077d_1_2892:u8 = low:u8(0:u8)
dsa_mem_ffaf077c_1_2893:u8 = low:u8(0:u8)
dsa_mem_ffaf077b_1_2894:u8 = low:u8(0:u8)
dsa_mem_ffaf077a_1_2895:u8 = low:u8(0:u8)
dsa_R_ZF_1_2896:bool = false
dsa_R_ESI_32_1_2897:u32 = 0xdce7505e:u32
dsa_R_AF_1_2898:bool = false
dsa_R_OF_1_2899:bool = false
dsa_R_SF_1_2900:bool = false
dsa_R_DF_1_2901:bool = false
dsa_R_EDI_32_1_2902:u32 = 0xffaf077a:u32
dsa_R_CF_1_2903:bool = true
dsa_R_EFLAGS_1_2904:u32 = 0x207:u32
dsa_R_PF_1_2905:bool = true
assert ~(dsa_R_ECX_32_1_2891:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp48"*/
label nocjmp48
dsa_mem_ffaf077a_1_2906:u8 =
  low:u8(pad:u32(dsa_mem_dce75061_1_2237:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75060_1_2236:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7505f_1_2235:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7505e_1_2234:u8))))
dsa_mem_ffaf077b_1_2907:u8 =
  low:u8((pad:u32(dsa_mem_dce75061_1_2237:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75060_1_2236:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7505f_1_2235:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7505e_1_2234:u8)))) >> 8:u32)
dsa_mem_ffaf077c_1_2908:u8 =
  low:u8((pad:u32(dsa_mem_dce75061_1_2237:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75060_1_2236:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7505f_1_2235:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7505e_1_2234:u8)))) >> 0x10:u32)
dsa_mem_ffaf077d_1_2909:u8 =
  low:u8((pad:u32(dsa_mem_dce75061_1_2237:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75060_1_2236:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7505f_1_2235:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7505e_1_2234:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2910:u32 =
  dsa_R_ESI_32_1_2897:u32 +
  (if dsa_R_DF_1_2901:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2911:u32 =
  dsa_R_EDI_32_1_2902:u32 +
  (if dsa_R_DF_1_2901:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2912:u32 = dsa_R_ECX_32_1_2891:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2912:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp47"*/
label nocjmp47
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf077e, 0, u32, rd
  @context "R_ESI_32" = 0xdce75062, 0, u32, rd
  @context "R_ECX_32" = 0x1d, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75062]" = 0x41, 99, u8, rd
  @context "mem32[0xdce75063]" = 0x41, 100, u8, rd
  @context "mem32[0xdce75064]" = 0x41, 101, u8, rd
  @context "mem32[0xdce75065]" = 0x41, 102, u8, rd
  @context "mem32[0xffaf077e]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf077f]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0780]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0781]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0781_1_2913:u8 = low:u8(0:u8)
dsa_mem_ffaf077e_1_2914:u8 = low:u8(0:u8)
dsa_mem_ffaf077f_1_2915:u8 = low:u8(0:u8)
dsa_mem_ffaf0780_1_2916:u8 = low:u8(0:u8)
dsa_R_ZF_1_2917:bool = false
dsa_R_ESI_32_1_2918:u32 = 0xdce75062:u32
dsa_R_AF_1_2919:bool = false
dsa_R_OF_1_2920:bool = false
dsa_R_SF_1_2921:bool = false
dsa_R_DF_1_2922:bool = false
dsa_R_EDI_32_1_2923:u32 = 0xffaf077e:u32
dsa_R_CF_1_2924:bool = true
dsa_R_EFLAGS_1_2925:u32 = 0x207:u32
dsa_R_PF_1_2926:bool = true
assert ~(dsa_R_ECX_32_1_2912:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp50"*/
label nocjmp50
dsa_mem_ffaf077e_1_2927:u8 =
  low:u8(pad:u32(dsa_mem_dce75065_1_2241:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75064_1_2240:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75063_1_2239:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75062_1_2238:u8))))
dsa_mem_ffaf077f_1_2928:u8 =
  low:u8((pad:u32(dsa_mem_dce75065_1_2241:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75064_1_2240:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75063_1_2239:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75062_1_2238:u8)))) >> 8:u32)
dsa_mem_ffaf0780_1_2929:u8 =
  low:u8((pad:u32(dsa_mem_dce75065_1_2241:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75064_1_2240:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75063_1_2239:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75062_1_2238:u8)))) >> 0x10:u32)
dsa_mem_ffaf0781_1_2930:u8 =
  low:u8((pad:u32(dsa_mem_dce75065_1_2241:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75064_1_2240:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75063_1_2239:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75062_1_2238:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2931:u32 =
  dsa_R_ESI_32_1_2918:u32 +
  (if dsa_R_DF_1_2922:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2932:u32 =
  dsa_R_EDI_32_1_2923:u32 +
  (if dsa_R_DF_1_2922:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2933:u32 = dsa_R_ECX_32_1_2912:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2933:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp49"*/
label nocjmp49
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0782, 0, u32, rd
  @context "R_ESI_32" = 0xdce75066, 0, u32, rd
  @context "R_ECX_32" = 0x1c, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75066]" = 0x41, 103, u8, rd
  @context "mem32[0xdce75067]" = 0x41, 104, u8, rd
  @context "mem32[0xdce75068]" = 0x41, 105, u8, rd
  @context "mem32[0xdce75069]" = 0x41, 106, u8, rd
  @context "mem32[0xffaf0782]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0783]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0784]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0785]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0782_1_2934:u8 = low:u8(0:u8)
dsa_mem_ffaf0784_1_2935:u8 = low:u8(0:u8)
dsa_mem_ffaf0785_1_2936:u8 = low:u8(0:u8)
dsa_mem_ffaf0783_1_2937:u8 = low:u8(0:u8)
dsa_R_ZF_1_2938:bool = false
dsa_R_ESI_32_1_2939:u32 = 0xdce75066:u32
dsa_R_AF_1_2940:bool = false
dsa_R_OF_1_2941:bool = false
dsa_R_SF_1_2942:bool = false
dsa_R_DF_1_2943:bool = false
dsa_R_EDI_32_1_2944:u32 = 0xffaf0782:u32
dsa_R_CF_1_2945:bool = true
dsa_R_EFLAGS_1_2946:u32 = 0x207:u32
dsa_R_PF_1_2947:bool = true
assert ~(dsa_R_ECX_32_1_2933:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp52"*/
label nocjmp52
dsa_mem_ffaf0782_1_2948:u8 =
  low:u8(pad:u32(dsa_mem_dce75069_1_2245:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75068_1_2244:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75067_1_2243:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75066_1_2242:u8))))
dsa_mem_ffaf0783_1_2949:u8 =
  low:u8((pad:u32(dsa_mem_dce75069_1_2245:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75068_1_2244:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75067_1_2243:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75066_1_2242:u8)))) >> 8:u32)
dsa_mem_ffaf0784_1_2950:u8 =
  low:u8((pad:u32(dsa_mem_dce75069_1_2245:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75068_1_2244:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75067_1_2243:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75066_1_2242:u8)))) >> 0x10:u32)
dsa_mem_ffaf0785_1_2951:u8 =
  low:u8((pad:u32(dsa_mem_dce75069_1_2245:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75068_1_2244:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75067_1_2243:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75066_1_2242:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2952:u32 =
  dsa_R_ESI_32_1_2939:u32 +
  (if dsa_R_DF_1_2943:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2953:u32 =
  dsa_R_EDI_32_1_2944:u32 +
  (if dsa_R_DF_1_2943:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2954:u32 = dsa_R_ECX_32_1_2933:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2954:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp51"*/
label nocjmp51
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0786, 0, u32, rd
  @context "R_ESI_32" = 0xdce7506a, 0, u32, rd
  @context "R_ECX_32" = 0x1b, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7506a]" = 0x41, 107, u8, rd
  @context "mem32[0xdce7506b]" = 0x41, 108, u8, rd
  @context "mem32[0xdce7506c]" = 0x41, 109, u8, rd
  @context "mem32[0xdce7506d]" = 0x41, 110, u8, rd
  @context "mem32[0xffaf0786]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0787]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0788]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0789]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0788_1_2955:u8 = low:u8(0:u8)
dsa_mem_ffaf0786_1_2956:u8 = low:u8(0:u8)
dsa_mem_ffaf0787_1_2957:u8 = low:u8(0:u8)
dsa_mem_ffaf0789_1_2958:u8 = low:u8(0:u8)
dsa_R_ZF_1_2959:bool = false
dsa_R_ESI_32_1_2960:u32 = 0xdce7506a:u32
dsa_R_AF_1_2961:bool = false
dsa_R_OF_1_2962:bool = false
dsa_R_SF_1_2963:bool = false
dsa_R_DF_1_2964:bool = false
dsa_R_EDI_32_1_2965:u32 = 0xffaf0786:u32
dsa_R_CF_1_2966:bool = true
dsa_R_EFLAGS_1_2967:u32 = 0x207:u32
dsa_R_PF_1_2968:bool = true
assert ~(dsa_R_ECX_32_1_2954:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp54"*/
label nocjmp54
dsa_mem_ffaf0786_1_2969:u8 =
  low:u8(pad:u32(dsa_mem_dce7506d_1_2249:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7506c_1_2248:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7506b_1_2247:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7506a_1_2246:u8))))
dsa_mem_ffaf0787_1_2970:u8 =
  low:u8((pad:u32(dsa_mem_dce7506d_1_2249:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7506c_1_2248:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7506b_1_2247:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7506a_1_2246:u8)))) >> 8:u32)
dsa_mem_ffaf0788_1_2971:u8 =
  low:u8((pad:u32(dsa_mem_dce7506d_1_2249:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7506c_1_2248:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7506b_1_2247:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7506a_1_2246:u8)))) >> 0x10:u32)
dsa_mem_ffaf0789_1_2972:u8 =
  low:u8((pad:u32(dsa_mem_dce7506d_1_2249:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7506c_1_2248:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7506b_1_2247:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7506a_1_2246:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2973:u32 =
  dsa_R_ESI_32_1_2960:u32 +
  (if dsa_R_DF_1_2964:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2974:u32 =
  dsa_R_EDI_32_1_2965:u32 +
  (if dsa_R_DF_1_2964:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2975:u32 = dsa_R_ECX_32_1_2954:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2975:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp53"*/
label nocjmp53
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf078a, 0, u32, rd
  @context "R_ESI_32" = 0xdce7506e, 0, u32, rd
  @context "R_ECX_32" = 0x1a, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7506e]" = 0x41, 111, u8, rd
  @context "mem32[0xdce7506f]" = 0x41, 112, u8, rd
  @context "mem32[0xdce75070]" = 0x41, 113, u8, rd
  @context "mem32[0xdce75071]" = 0x41, 114, u8, rd
  @context "mem32[0xffaf078a]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf078b]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf078c]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf078d]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf078d_1_2976:u8 = low:u8(0:u8)
dsa_mem_ffaf078b_1_2977:u8 = low:u8(0:u8)
dsa_mem_ffaf078a_1_2978:u8 = low:u8(0:u8)
dsa_mem_ffaf078c_1_2979:u8 = low:u8(0:u8)
dsa_R_ZF_1_2980:bool = false
dsa_R_ESI_32_1_2981:u32 = 0xdce7506e:u32
dsa_R_AF_1_2982:bool = false
dsa_R_OF_1_2983:bool = false
dsa_R_SF_1_2984:bool = false
dsa_R_DF_1_2985:bool = false
dsa_R_EDI_32_1_2986:u32 = 0xffaf078a:u32
dsa_R_CF_1_2987:bool = true
dsa_R_EFLAGS_1_2988:u32 = 0x207:u32
dsa_R_PF_1_2989:bool = true
assert ~(dsa_R_ECX_32_1_2975:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp56"*/
label nocjmp56
dsa_mem_ffaf078a_1_2990:u8 =
  low:u8(pad:u32(dsa_mem_dce75071_1_2253:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75070_1_2252:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7506f_1_2251:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7506e_1_2250:u8))))
dsa_mem_ffaf078b_1_2991:u8 =
  low:u8((pad:u32(dsa_mem_dce75071_1_2253:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75070_1_2252:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7506f_1_2251:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7506e_1_2250:u8)))) >> 8:u32)
dsa_mem_ffaf078c_1_2992:u8 =
  low:u8((pad:u32(dsa_mem_dce75071_1_2253:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75070_1_2252:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7506f_1_2251:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7506e_1_2250:u8)))) >> 0x10:u32)
dsa_mem_ffaf078d_1_2993:u8 =
  low:u8((pad:u32(dsa_mem_dce75071_1_2253:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75070_1_2252:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7506f_1_2251:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7506e_1_2250:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_2994:u32 =
  dsa_R_ESI_32_1_2981:u32 +
  (if dsa_R_DF_1_2985:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_2995:u32 =
  dsa_R_EDI_32_1_2986:u32 +
  (if dsa_R_DF_1_2985:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_2996:u32 = dsa_R_ECX_32_1_2975:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_2996:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp55"*/
label nocjmp55
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf078e, 0, u32, rd
  @context "R_ESI_32" = 0xdce75072, 0, u32, rd
  @context "R_ECX_32" = 0x19, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75072]" = 0x41, 115, u8, rd
  @context "mem32[0xdce75073]" = 0x41, 116, u8, rd
  @context "mem32[0xdce75074]" = 0x41, 117, u8, rd
  @context "mem32[0xdce75075]" = 0x41, 118, u8, rd
  @context "mem32[0xffaf078e]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf078f]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0790]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0791]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0791_1_2997:u8 = low:u8(0:u8)
dsa_mem_ffaf0790_1_2998:u8 = low:u8(0:u8)
dsa_mem_ffaf078e_1_2999:u8 = low:u8(0:u8)
dsa_mem_ffaf078f_1_3000:u8 = low:u8(0:u8)
dsa_R_ZF_1_3001:bool = false
dsa_R_ESI_32_1_3002:u32 = 0xdce75072:u32
dsa_R_AF_1_3003:bool = false
dsa_R_OF_1_3004:bool = false
dsa_R_SF_1_3005:bool = false
dsa_R_DF_1_3006:bool = false
dsa_R_EDI_32_1_3007:u32 = 0xffaf078e:u32
dsa_R_CF_1_3008:bool = true
dsa_R_EFLAGS_1_3009:u32 = 0x207:u32
dsa_R_PF_1_3010:bool = true
assert ~(dsa_R_ECX_32_1_2996:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp58"*/
label nocjmp58
dsa_mem_ffaf078e_1_3011:u8 =
  low:u8(pad:u32(dsa_mem_dce75075_1_2257:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75074_1_2256:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75073_1_2255:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75072_1_2254:u8))))
dsa_mem_ffaf078f_1_3012:u8 =
  low:u8((pad:u32(dsa_mem_dce75075_1_2257:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75074_1_2256:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75073_1_2255:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75072_1_2254:u8)))) >> 8:u32)
dsa_mem_ffaf0790_1_3013:u8 =
  low:u8((pad:u32(dsa_mem_dce75075_1_2257:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75074_1_2256:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75073_1_2255:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75072_1_2254:u8)))) >> 0x10:u32)
dsa_mem_ffaf0791_1_3014:u8 =
  low:u8((pad:u32(dsa_mem_dce75075_1_2257:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75074_1_2256:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75073_1_2255:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75072_1_2254:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3015:u32 =
  dsa_R_ESI_32_1_3002:u32 +
  (if dsa_R_DF_1_3006:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3016:u32 =
  dsa_R_EDI_32_1_3007:u32 +
  (if dsa_R_DF_1_3006:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3017:u32 = dsa_R_ECX_32_1_2996:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3017:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp57"*/
label nocjmp57
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0792, 0, u32, rd
  @context "R_ESI_32" = 0xdce75076, 0, u32, rd
  @context "R_ECX_32" = 0x18, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75076]" = 0x41, 119, u8, rd
  @context "mem32[0xdce75077]" = 0x41, 120, u8, rd
  @context "mem32[0xdce75078]" = 0x41, 121, u8, rd
  @context "mem32[0xdce75079]" = 0x41, 122, u8, rd
  @context "mem32[0xffaf0792]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0793]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0794]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0795]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0795_1_3018:u8 = low:u8(0:u8)
dsa_mem_ffaf0794_1_3019:u8 = low:u8(0:u8)
dsa_mem_ffaf0792_1_3020:u8 = low:u8(0:u8)
dsa_mem_ffaf0793_1_3021:u8 = low:u8(0:u8)
dsa_R_ZF_1_3022:bool = false
dsa_R_ESI_32_1_3023:u32 = 0xdce75076:u32
dsa_R_AF_1_3024:bool = false
dsa_R_OF_1_3025:bool = false
dsa_R_SF_1_3026:bool = false
dsa_R_DF_1_3027:bool = false
dsa_R_EDI_32_1_3028:u32 = 0xffaf0792:u32
dsa_R_CF_1_3029:bool = true
dsa_R_EFLAGS_1_3030:u32 = 0x207:u32
dsa_R_PF_1_3031:bool = true
assert ~(dsa_R_ECX_32_1_3017:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp60"*/
label nocjmp60
dsa_mem_ffaf0792_1_3032:u8 =
  low:u8(pad:u32(dsa_mem_dce75079_1_2261:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75078_1_2260:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75077_1_2259:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75076_1_2258:u8))))
dsa_mem_ffaf0793_1_3033:u8 =
  low:u8((pad:u32(dsa_mem_dce75079_1_2261:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75078_1_2260:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75077_1_2259:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75076_1_2258:u8)))) >> 8:u32)
dsa_mem_ffaf0794_1_3034:u8 =
  low:u8((pad:u32(dsa_mem_dce75079_1_2261:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75078_1_2260:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75077_1_2259:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75076_1_2258:u8)))) >> 0x10:u32)
dsa_mem_ffaf0795_1_3035:u8 =
  low:u8((pad:u32(dsa_mem_dce75079_1_2261:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75078_1_2260:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75077_1_2259:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75076_1_2258:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3036:u32 =
  dsa_R_ESI_32_1_3023:u32 +
  (if dsa_R_DF_1_3027:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3037:u32 =
  dsa_R_EDI_32_1_3028:u32 +
  (if dsa_R_DF_1_3027:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3038:u32 = dsa_R_ECX_32_1_3017:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3038:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp59"*/
label nocjmp59
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf0796, 0, u32, rd
  @context "R_ESI_32" = 0xdce7507a, 0, u32, rd
  @context "R_ECX_32" = 0x17, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7507a]" = 0x41, 123, u8, rd
  @context "mem32[0xdce7507b]" = 0x41, 124, u8, rd
  @context "mem32[0xdce7507c]" = 0x41, 125, u8, rd
  @context "mem32[0xdce7507d]" = 0x41, 126, u8, rd
  @context "mem32[0xffaf0796]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0797]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0798]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf0799]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf0798_1_3039:u8 = low:u8(0:u8)
dsa_mem_ffaf0799_1_3040:u8 = low:u8(0:u8)
dsa_mem_ffaf0796_1_3041:u8 = low:u8(0:u8)
dsa_mem_ffaf0797_1_3042:u8 = low:u8(0:u8)
dsa_R_ZF_1_3043:bool = false
dsa_R_ESI_32_1_3044:u32 = 0xdce7507a:u32
dsa_R_AF_1_3045:bool = false
dsa_R_OF_1_3046:bool = false
dsa_R_SF_1_3047:bool = false
dsa_R_DF_1_3048:bool = false
dsa_R_EDI_32_1_3049:u32 = 0xffaf0796:u32
dsa_R_CF_1_3050:bool = true
dsa_R_EFLAGS_1_3051:u32 = 0x207:u32
dsa_R_PF_1_3052:bool = true
assert ~(dsa_R_ECX_32_1_3038:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp62"*/
label nocjmp62
dsa_mem_ffaf0796_1_3053:u8 =
  low:u8(pad:u32(dsa_mem_dce7507d_1_2265:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7507c_1_2264:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7507b_1_2263:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7507a_1_2262:u8))))
dsa_mem_ffaf0797_1_3054:u8 =
  low:u8((pad:u32(dsa_mem_dce7507d_1_2265:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7507c_1_2264:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7507b_1_2263:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7507a_1_2262:u8)))) >> 8:u32)
dsa_mem_ffaf0798_1_3055:u8 =
  low:u8((pad:u32(dsa_mem_dce7507d_1_2265:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7507c_1_2264:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7507b_1_2263:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7507a_1_2262:u8)))) >> 0x10:u32)
dsa_mem_ffaf0799_1_3056:u8 =
  low:u8((pad:u32(dsa_mem_dce7507d_1_2265:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7507c_1_2264:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7507b_1_2263:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7507a_1_2262:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3057:u32 =
  dsa_R_ESI_32_1_3044:u32 +
  (if dsa_R_DF_1_3048:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3058:u32 =
  dsa_R_EDI_32_1_3049:u32 +
  (if dsa_R_DF_1_3048:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3059:u32 = dsa_R_ECX_32_1_3038:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3059:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp61"*/
label nocjmp61
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf079a, 0, u32, rd
  @context "R_ESI_32" = 0xdce7507e, 0, u32, rd
  @context "R_ECX_32" = 0x16, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7507e]" = 0x41, 127, u8, rd
  @context "mem32[0xdce7507f]" = 0x41, 128, u8, rd
  @context "mem32[0xdce75080]" = 0x41, 129, u8, rd
  @context "mem32[0xdce75081]" = 0x41, 130, u8, rd
  @context "mem32[0xffaf079a]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf079b]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf079c]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf079d]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf079d_1_3060:u8 = low:u8(0:u8)
dsa_mem_ffaf079a_1_3061:u8 = low:u8(0:u8)
dsa_mem_ffaf079c_1_3062:u8 = low:u8(0:u8)
dsa_mem_ffaf079b_1_3063:u8 = low:u8(0:u8)
dsa_R_ZF_1_3064:bool = false
dsa_R_ESI_32_1_3065:u32 = 0xdce7507e:u32
dsa_R_AF_1_3066:bool = false
dsa_R_OF_1_3067:bool = false
dsa_R_SF_1_3068:bool = false
dsa_R_DF_1_3069:bool = false
dsa_R_EDI_32_1_3070:u32 = 0xffaf079a:u32
dsa_R_CF_1_3071:bool = true
dsa_R_EFLAGS_1_3072:u32 = 0x207:u32
dsa_R_PF_1_3073:bool = true
assert ~(dsa_R_ECX_32_1_3059:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp64"*/
label nocjmp64
dsa_mem_ffaf079a_1_3074:u8 =
  low:u8(pad:u32(dsa_mem_dce75081_1_2269:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75080_1_2268:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7507f_1_2267:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7507e_1_2266:u8))))
dsa_mem_ffaf079b_1_3075:u8 =
  low:u8((pad:u32(dsa_mem_dce75081_1_2269:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75080_1_2268:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7507f_1_2267:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7507e_1_2266:u8)))) >> 8:u32)
dsa_mem_ffaf079c_1_3076:u8 =
  low:u8((pad:u32(dsa_mem_dce75081_1_2269:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75080_1_2268:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7507f_1_2267:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7507e_1_2266:u8)))) >> 0x10:u32)
dsa_mem_ffaf079d_1_3077:u8 =
  low:u8((pad:u32(dsa_mem_dce75081_1_2269:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75080_1_2268:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7507f_1_2267:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7507e_1_2266:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3078:u32 =
  dsa_R_ESI_32_1_3065:u32 +
  (if dsa_R_DF_1_3069:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3079:u32 =
  dsa_R_EDI_32_1_3070:u32 +
  (if dsa_R_DF_1_3069:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3080:u32 = dsa_R_ECX_32_1_3059:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3080:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp63"*/
label nocjmp63
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf079e, 0, u32, rd
  @context "R_ESI_32" = 0xdce75082, 0, u32, rd
  @context "R_ECX_32" = 0x15, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75082]" = 0x41, 131, u8, rd
  @context "mem32[0xdce75083]" = 0x41, 132, u8, rd
  @context "mem32[0xdce75084]" = 0x41, 133, u8, rd
  @context "mem32[0xdce75085]" = 0x41, 134, u8, rd
  @context "mem32[0xffaf079e]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf079f]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07a0]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07a1]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07a0_1_3081:u8 = low:u8(0:u8)
dsa_mem_ffaf079f_1_3082:u8 = low:u8(0:u8)
dsa_mem_ffaf079e_1_3083:u8 = low:u8(0:u8)
dsa_mem_ffaf07a1_1_3084:u8 = low:u8(0:u8)
dsa_R_ZF_1_3085:bool = false
dsa_R_ESI_32_1_3086:u32 = 0xdce75082:u32
dsa_R_AF_1_3087:bool = false
dsa_R_OF_1_3088:bool = false
dsa_R_SF_1_3089:bool = false
dsa_R_DF_1_3090:bool = false
dsa_R_EDI_32_1_3091:u32 = 0xffaf079e:u32
dsa_R_CF_1_3092:bool = true
dsa_R_EFLAGS_1_3093:u32 = 0x207:u32
dsa_R_PF_1_3094:bool = true
assert ~(dsa_R_ECX_32_1_3080:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp66"*/
label nocjmp66
dsa_mem_ffaf079e_1_3095:u8 =
  low:u8(pad:u32(dsa_mem_dce75085_1_2273:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75084_1_2272:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75083_1_2271:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75082_1_2270:u8))))
dsa_mem_ffaf079f_1_3096:u8 =
  low:u8((pad:u32(dsa_mem_dce75085_1_2273:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75084_1_2272:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75083_1_2271:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75082_1_2270:u8)))) >> 8:u32)
dsa_mem_ffaf07a0_1_3097:u8 =
  low:u8((pad:u32(dsa_mem_dce75085_1_2273:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75084_1_2272:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75083_1_2271:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75082_1_2270:u8)))) >> 0x10:u32)
dsa_mem_ffaf07a1_1_3098:u8 =
  low:u8((pad:u32(dsa_mem_dce75085_1_2273:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75084_1_2272:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75083_1_2271:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75082_1_2270:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3099:u32 =
  dsa_R_ESI_32_1_3086:u32 +
  (if dsa_R_DF_1_3090:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3100:u32 =
  dsa_R_EDI_32_1_3091:u32 +
  (if dsa_R_DF_1_3090:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3101:u32 = dsa_R_ECX_32_1_3080:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3101:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp65"*/
label nocjmp65
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07a2, 0, u32, rd
  @context "R_ESI_32" = 0xdce75086, 0, u32, rd
  @context "R_ECX_32" = 0x14, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75086]" = 0x41, 135, u8, rd
  @context "mem32[0xdce75087]" = 0x41, 136, u8, rd
  @context "mem32[0xdce75088]" = 0x41, 137, u8, rd
  @context "mem32[0xdce75089]" = 0x41, 138, u8, rd
  @context "mem32[0xffaf07a2]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07a3]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07a4]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07a5]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07a5_1_3102:u8 = low:u8(0:u8)
dsa_mem_ffaf07a4_1_3103:u8 = low:u8(0:u8)
dsa_mem_ffaf07a3_1_3104:u8 = low:u8(0:u8)
dsa_mem_ffaf07a2_1_3105:u8 = low:u8(0:u8)
dsa_R_ZF_1_3106:bool = false
dsa_R_ESI_32_1_3107:u32 = 0xdce75086:u32
dsa_R_AF_1_3108:bool = false
dsa_R_OF_1_3109:bool = false
dsa_R_SF_1_3110:bool = false
dsa_R_DF_1_3111:bool = false
dsa_R_EDI_32_1_3112:u32 = 0xffaf07a2:u32
dsa_R_CF_1_3113:bool = true
dsa_R_EFLAGS_1_3114:u32 = 0x207:u32
dsa_R_PF_1_3115:bool = true
assert ~(dsa_R_ECX_32_1_3101:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp68"*/
label nocjmp68
dsa_mem_ffaf07a2_1_3116:u8 =
  low:u8(pad:u32(dsa_mem_dce75089_1_2277:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75088_1_2276:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75087_1_2275:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75086_1_2274:u8))))
dsa_mem_ffaf07a3_1_3117:u8 =
  low:u8((pad:u32(dsa_mem_dce75089_1_2277:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75088_1_2276:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75087_1_2275:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75086_1_2274:u8)))) >> 8:u32)
dsa_mem_ffaf07a4_1_3118:u8 =
  low:u8((pad:u32(dsa_mem_dce75089_1_2277:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75088_1_2276:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75087_1_2275:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75086_1_2274:u8)))) >> 0x10:u32)
dsa_mem_ffaf07a5_1_3119:u8 =
  low:u8((pad:u32(dsa_mem_dce75089_1_2277:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75088_1_2276:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75087_1_2275:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75086_1_2274:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3120:u32 =
  dsa_R_ESI_32_1_3107:u32 +
  (if dsa_R_DF_1_3111:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3121:u32 =
  dsa_R_EDI_32_1_3112:u32 +
  (if dsa_R_DF_1_3111:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3122:u32 = dsa_R_ECX_32_1_3101:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3122:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp67"*/
label nocjmp67
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07a6, 0, u32, rd
  @context "R_ESI_32" = 0xdce7508a, 0, u32, rd
  @context "R_ECX_32" = 0x13, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7508a]" = 0x41, 139, u8, rd
  @context "mem32[0xdce7508b]" = 0x41, 140, u8, rd
  @context "mem32[0xdce7508c]" = 0x41, 141, u8, rd
  @context "mem32[0xdce7508d]" = 0x41, 142, u8, rd
  @context "mem32[0xffaf07a6]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07a7]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07a8]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07a9]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07a8_1_3123:u8 = low:u8(0:u8)
dsa_mem_ffaf07a6_1_3124:u8 = low:u8(0:u8)
dsa_mem_ffaf07a9_1_3125:u8 = low:u8(0:u8)
dsa_mem_ffaf07a7_1_3126:u8 = low:u8(0:u8)
dsa_R_ZF_1_3127:bool = false
dsa_R_ESI_32_1_3128:u32 = 0xdce7508a:u32
dsa_R_AF_1_3129:bool = false
dsa_R_OF_1_3130:bool = false
dsa_R_SF_1_3131:bool = false
dsa_R_DF_1_3132:bool = false
dsa_R_EDI_32_1_3133:u32 = 0xffaf07a6:u32
dsa_R_CF_1_3134:bool = true
dsa_R_EFLAGS_1_3135:u32 = 0x207:u32
dsa_R_PF_1_3136:bool = true
assert ~(dsa_R_ECX_32_1_3122:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp70"*/
label nocjmp70
dsa_mem_ffaf07a6_1_3137:u8 =
  low:u8(pad:u32(dsa_mem_dce7508d_1_2281:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7508c_1_2280:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7508b_1_2279:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7508a_1_2278:u8))))
dsa_mem_ffaf07a7_1_3138:u8 =
  low:u8((pad:u32(dsa_mem_dce7508d_1_2281:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7508c_1_2280:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7508b_1_2279:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7508a_1_2278:u8)))) >> 8:u32)
dsa_mem_ffaf07a8_1_3139:u8 =
  low:u8((pad:u32(dsa_mem_dce7508d_1_2281:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7508c_1_2280:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7508b_1_2279:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7508a_1_2278:u8)))) >> 0x10:u32)
dsa_mem_ffaf07a9_1_3140:u8 =
  low:u8((pad:u32(dsa_mem_dce7508d_1_2281:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7508c_1_2280:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7508b_1_2279:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7508a_1_2278:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3141:u32 =
  dsa_R_ESI_32_1_3128:u32 +
  (if dsa_R_DF_1_3132:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3142:u32 =
  dsa_R_EDI_32_1_3133:u32 +
  (if dsa_R_DF_1_3132:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3143:u32 = dsa_R_ECX_32_1_3122:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3143:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp69"*/
label nocjmp69
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07aa, 0, u32, rd
  @context "R_ESI_32" = 0xdce7508e, 0, u32, rd
  @context "R_ECX_32" = 0x12, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7508e]" = 0x41, 143, u8, rd
  @context "mem32[0xdce7508f]" = 0x41, 144, u8, rd
  @context "mem32[0xdce75090]" = 0x41, 145, u8, rd
  @context "mem32[0xdce75091]" = 0x41, 146, u8, rd
  @context "mem32[0xffaf07aa]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07ab]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07ac]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07ad]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07aa_1_3144:u8 = low:u8(0:u8)
dsa_mem_ffaf07ab_1_3145:u8 = low:u8(0:u8)
dsa_mem_ffaf07ac_1_3146:u8 = low:u8(0:u8)
dsa_mem_ffaf07ad_1_3147:u8 = low:u8(0:u8)
dsa_R_ZF_1_3148:bool = false
dsa_R_ESI_32_1_3149:u32 = 0xdce7508e:u32
dsa_R_AF_1_3150:bool = false
dsa_R_OF_1_3151:bool = false
dsa_R_SF_1_3152:bool = false
dsa_R_DF_1_3153:bool = false
dsa_R_EDI_32_1_3154:u32 = 0xffaf07aa:u32
dsa_R_CF_1_3155:bool = true
dsa_R_EFLAGS_1_3156:u32 = 0x207:u32
dsa_R_PF_1_3157:bool = true
assert ~(dsa_R_ECX_32_1_3143:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp72"*/
label nocjmp72
dsa_mem_ffaf07aa_1_3158:u8 =
  low:u8(pad:u32(dsa_mem_dce75091_1_2285:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75090_1_2284:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7508f_1_2283:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7508e_1_2282:u8))))
dsa_mem_ffaf07ab_1_3159:u8 =
  low:u8((pad:u32(dsa_mem_dce75091_1_2285:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75090_1_2284:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7508f_1_2283:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7508e_1_2282:u8)))) >> 8:u32)
dsa_mem_ffaf07ac_1_3160:u8 =
  low:u8((pad:u32(dsa_mem_dce75091_1_2285:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75090_1_2284:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7508f_1_2283:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7508e_1_2282:u8)))) >> 0x10:u32)
dsa_mem_ffaf07ad_1_3161:u8 =
  low:u8((pad:u32(dsa_mem_dce75091_1_2285:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75090_1_2284:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7508f_1_2283:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7508e_1_2282:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3162:u32 =
  dsa_R_ESI_32_1_3149:u32 +
  (if dsa_R_DF_1_3153:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3163:u32 =
  dsa_R_EDI_32_1_3154:u32 +
  (if dsa_R_DF_1_3153:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3164:u32 = dsa_R_ECX_32_1_3143:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3164:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp71"*/
label nocjmp71
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07ae, 0, u32, rd
  @context "R_ESI_32" = 0xdce75092, 0, u32, rd
  @context "R_ECX_32" = 0x11, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75092]" = 0x41, 147, u8, rd
  @context "mem32[0xdce75093]" = 0x41, 148, u8, rd
  @context "mem32[0xdce75094]" = 0x41, 149, u8, rd
  @context "mem32[0xdce75095]" = 0x41, 150, u8, rd
  @context "mem32[0xffaf07ae]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07af]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07b0]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07b1]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07b0_1_3165:u8 = low:u8(0:u8)
dsa_mem_ffaf07af_1_3166:u8 = low:u8(0:u8)
dsa_mem_ffaf07b1_1_3167:u8 = low:u8(0:u8)
dsa_mem_ffaf07ae_1_3168:u8 = low:u8(0:u8)
dsa_R_ZF_1_3169:bool = false
dsa_R_ESI_32_1_3170:u32 = 0xdce75092:u32
dsa_R_AF_1_3171:bool = false
dsa_R_OF_1_3172:bool = false
dsa_R_SF_1_3173:bool = false
dsa_R_DF_1_3174:bool = false
dsa_R_EDI_32_1_3175:u32 = 0xffaf07ae:u32
dsa_R_CF_1_3176:bool = true
dsa_R_EFLAGS_1_3177:u32 = 0x207:u32
dsa_R_PF_1_3178:bool = true
assert ~(dsa_R_ECX_32_1_3164:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp74"*/
label nocjmp74
dsa_mem_ffaf07ae_1_3179:u8 =
  low:u8(pad:u32(dsa_mem_dce75095_1_2289:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75094_1_2288:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75093_1_2287:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75092_1_2286:u8))))
dsa_mem_ffaf07af_1_3180:u8 =
  low:u8((pad:u32(dsa_mem_dce75095_1_2289:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75094_1_2288:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75093_1_2287:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75092_1_2286:u8)))) >> 8:u32)
dsa_mem_ffaf07b0_1_3181:u8 =
  low:u8((pad:u32(dsa_mem_dce75095_1_2289:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75094_1_2288:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75093_1_2287:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75092_1_2286:u8)))) >> 0x10:u32)
dsa_mem_ffaf07b1_1_3182:u8 =
  low:u8((pad:u32(dsa_mem_dce75095_1_2289:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75094_1_2288:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75093_1_2287:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75092_1_2286:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3183:u32 =
  dsa_R_ESI_32_1_3170:u32 +
  (if dsa_R_DF_1_3174:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3184:u32 =
  dsa_R_EDI_32_1_3175:u32 +
  (if dsa_R_DF_1_3174:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3185:u32 = dsa_R_ECX_32_1_3164:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3185:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp73"*/
label nocjmp73
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07b2, 0, u32, rd
  @context "R_ESI_32" = 0xdce75096, 0, u32, rd
  @context "R_ECX_32" = 0x10, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce75096]" = 0x41, 151, u8, rd
  @context "mem32[0xdce75097]" = 0x41, 152, u8, rd
  @context "mem32[0xdce75098]" = 0x41, 153, u8, rd
  @context "mem32[0xdce75099]" = 0x41, 154, u8, rd
  @context "mem32[0xffaf07b2]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07b3]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07b4]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07b5]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07b5_1_3186:u8 = low:u8(0:u8)
dsa_mem_ffaf07b2_1_3187:u8 = low:u8(0:u8)
dsa_mem_ffaf07b3_1_3188:u8 = low:u8(0:u8)
dsa_mem_ffaf07b4_1_3189:u8 = low:u8(0:u8)
dsa_R_ZF_1_3190:bool = false
dsa_R_ESI_32_1_3191:u32 = 0xdce75096:u32
dsa_R_AF_1_3192:bool = false
dsa_R_OF_1_3193:bool = false
dsa_R_SF_1_3194:bool = false
dsa_R_DF_1_3195:bool = false
dsa_R_EDI_32_1_3196:u32 = 0xffaf07b2:u32
dsa_R_CF_1_3197:bool = true
dsa_R_EFLAGS_1_3198:u32 = 0x207:u32
dsa_R_PF_1_3199:bool = true
assert ~(dsa_R_ECX_32_1_3185:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp76"*/
label nocjmp76
dsa_mem_ffaf07b2_1_3200:u8 =
  low:u8(pad:u32(dsa_mem_dce75099_1_2293:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75098_1_2292:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75097_1_2291:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75096_1_2290:u8))))
dsa_mem_ffaf07b3_1_3201:u8 =
  low:u8((pad:u32(dsa_mem_dce75099_1_2293:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75098_1_2292:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75097_1_2291:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75096_1_2290:u8)))) >> 8:u32)
dsa_mem_ffaf07b4_1_3202:u8 =
  low:u8((pad:u32(dsa_mem_dce75099_1_2293:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75098_1_2292:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75097_1_2291:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75096_1_2290:u8)))) >> 0x10:u32)
dsa_mem_ffaf07b5_1_3203:u8 =
  low:u8((pad:u32(dsa_mem_dce75099_1_2293:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce75098_1_2292:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce75097_1_2291:u8) << 8:u32 |
         pad:u32(dsa_mem_dce75096_1_2290:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3204:u32 =
  dsa_R_ESI_32_1_3191:u32 +
  (if dsa_R_DF_1_3195:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3205:u32 =
  dsa_R_EDI_32_1_3196:u32 +
  (if dsa_R_DF_1_3195:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3206:u32 = dsa_R_ECX_32_1_3185:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3206:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp75"*/
label nocjmp75
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07b6, 0, u32, rd
  @context "R_ESI_32" = 0xdce7509a, 0, u32, rd
  @context "R_ECX_32" = 0xf, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7509a]" = 0x41, 155, u8, rd
  @context "mem32[0xdce7509b]" = 0x41, 156, u8, rd
  @context "mem32[0xdce7509c]" = 0x41, 157, u8, rd
  @context "mem32[0xdce7509d]" = 0x41, 158, u8, rd
  @context "mem32[0xffaf07b6]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07b7]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07b8]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07b9]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07b7_1_3207:u8 = low:u8(0:u8)
dsa_mem_ffaf07b8_1_3208:u8 = low:u8(0:u8)
dsa_mem_ffaf07b6_1_3209:u8 = low:u8(0:u8)
dsa_mem_ffaf07b9_1_3210:u8 = low:u8(0:u8)
dsa_R_ZF_1_3211:bool = false
dsa_R_ESI_32_1_3212:u32 = 0xdce7509a:u32
dsa_R_AF_1_3213:bool = false
dsa_R_OF_1_3214:bool = false
dsa_R_SF_1_3215:bool = false
dsa_R_DF_1_3216:bool = false
dsa_R_EDI_32_1_3217:u32 = 0xffaf07b6:u32
dsa_R_CF_1_3218:bool = true
dsa_R_EFLAGS_1_3219:u32 = 0x207:u32
dsa_R_PF_1_3220:bool = true
assert ~(dsa_R_ECX_32_1_3206:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp78"*/
label nocjmp78
dsa_mem_ffaf07b6_1_3221:u8 =
  low:u8(pad:u32(dsa_mem_dce7509d_1_2297:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7509c_1_2296:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7509b_1_2295:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7509a_1_2294:u8))))
dsa_mem_ffaf07b7_1_3222:u8 =
  low:u8((pad:u32(dsa_mem_dce7509d_1_2297:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7509c_1_2296:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7509b_1_2295:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7509a_1_2294:u8)))) >> 8:u32)
dsa_mem_ffaf07b8_1_3223:u8 =
  low:u8((pad:u32(dsa_mem_dce7509d_1_2297:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7509c_1_2296:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7509b_1_2295:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7509a_1_2294:u8)))) >> 0x10:u32)
dsa_mem_ffaf07b9_1_3224:u8 =
  low:u8((pad:u32(dsa_mem_dce7509d_1_2297:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce7509c_1_2296:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7509b_1_2295:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7509a_1_2294:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3225:u32 =
  dsa_R_ESI_32_1_3212:u32 +
  (if dsa_R_DF_1_3216:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3226:u32 =
  dsa_R_EDI_32_1_3217:u32 +
  (if dsa_R_DF_1_3216:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3227:u32 = dsa_R_ECX_32_1_3206:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3227:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp77"*/
label nocjmp77
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07ba, 0, u32, rd
  @context "R_ESI_32" = 0xdce7509e, 0, u32, rd
  @context "R_ECX_32" = 0xe, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce7509e]" = 0x41, 159, u8, rd
  @context "mem32[0xdce7509f]" = 0x41, 160, u8, rd
  @context "mem32[0xdce750a0]" = 0x41, 161, u8, rd
  @context "mem32[0xdce750a1]" = 0x41, 162, u8, rd
  @context "mem32[0xffaf07ba]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07bb]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07bc]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07bd]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07ba_1_3228:u8 = low:u8(0:u8)
dsa_mem_ffaf07bc_1_3229:u8 = low:u8(0:u8)
dsa_mem_ffaf07bb_1_3230:u8 = low:u8(0:u8)
dsa_mem_ffaf07bd_1_3231:u8 = low:u8(0:u8)
dsa_R_ZF_1_3232:bool = false
dsa_R_ESI_32_1_3233:u32 = 0xdce7509e:u32
dsa_R_AF_1_3234:bool = false
dsa_R_OF_1_3235:bool = false
dsa_R_SF_1_3236:bool = false
dsa_R_DF_1_3237:bool = false
dsa_R_EDI_32_1_3238:u32 = 0xffaf07ba:u32
dsa_R_CF_1_3239:bool = true
dsa_R_EFLAGS_1_3240:u32 = 0x207:u32
dsa_R_PF_1_3241:bool = true
assert ~(dsa_R_ECX_32_1_3227:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp80"*/
label nocjmp80
dsa_mem_ffaf07ba_1_3242:u8 =
  low:u8(pad:u32(dsa_mem_dce750a1_1_2301:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750a0_1_2300:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7509f_1_2299:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7509e_1_2298:u8))))
dsa_mem_ffaf07bb_1_3243:u8 =
  low:u8((pad:u32(dsa_mem_dce750a1_1_2301:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750a0_1_2300:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7509f_1_2299:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7509e_1_2298:u8)))) >> 8:u32)
dsa_mem_ffaf07bc_1_3244:u8 =
  low:u8((pad:u32(dsa_mem_dce750a1_1_2301:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750a0_1_2300:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7509f_1_2299:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7509e_1_2298:u8)))) >> 0x10:u32)
dsa_mem_ffaf07bd_1_3245:u8 =
  low:u8((pad:u32(dsa_mem_dce750a1_1_2301:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750a0_1_2300:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce7509f_1_2299:u8) << 8:u32 |
         pad:u32(dsa_mem_dce7509e_1_2298:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3246:u32 =
  dsa_R_ESI_32_1_3233:u32 +
  (if dsa_R_DF_1_3237:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3247:u32 =
  dsa_R_EDI_32_1_3238:u32 +
  (if dsa_R_DF_1_3237:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3248:u32 = dsa_R_ECX_32_1_3227:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3248:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp79"*/
label nocjmp79
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07be, 0, u32, rd
  @context "R_ESI_32" = 0xdce750a2, 0, u32, rd
  @context "R_ECX_32" = 0xd, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750a2]" = 0x41, 163, u8, rd
  @context "mem32[0xdce750a3]" = 0x41, 164, u8, rd
  @context "mem32[0xdce750a4]" = 0x41, 165, u8, rd
  @context "mem32[0xdce750a5]" = 0x41, 166, u8, rd
  @context "mem32[0xffaf07be]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07bf]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07c0]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07c1]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07c0_1_3249:u8 = low:u8(0:u8)
dsa_mem_ffaf07bf_1_3250:u8 = low:u8(0:u8)
dsa_mem_ffaf07c1_1_3251:u8 = low:u8(0:u8)
dsa_mem_ffaf07be_1_3252:u8 = low:u8(0:u8)
dsa_R_ZF_1_3253:bool = false
dsa_R_ESI_32_1_3254:u32 = 0xdce750a2:u32
dsa_R_AF_1_3255:bool = false
dsa_R_OF_1_3256:bool = false
dsa_R_SF_1_3257:bool = false
dsa_R_DF_1_3258:bool = false
dsa_R_EDI_32_1_3259:u32 = 0xffaf07be:u32
dsa_R_CF_1_3260:bool = true
dsa_R_EFLAGS_1_3261:u32 = 0x207:u32
dsa_R_PF_1_3262:bool = true
assert ~(dsa_R_ECX_32_1_3248:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp82"*/
label nocjmp82
dsa_mem_ffaf07be_1_3263:u8 =
  low:u8(pad:u32(dsa_mem_dce750a5_1_2305:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750a4_1_2304:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750a3_1_2303:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750a2_1_2302:u8))))
dsa_mem_ffaf07bf_1_3264:u8 =
  low:u8((pad:u32(dsa_mem_dce750a5_1_2305:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750a4_1_2304:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750a3_1_2303:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750a2_1_2302:u8)))) >> 8:u32)
dsa_mem_ffaf07c0_1_3265:u8 =
  low:u8((pad:u32(dsa_mem_dce750a5_1_2305:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750a4_1_2304:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750a3_1_2303:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750a2_1_2302:u8)))) >> 0x10:u32)
dsa_mem_ffaf07c1_1_3266:u8 =
  low:u8((pad:u32(dsa_mem_dce750a5_1_2305:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750a4_1_2304:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750a3_1_2303:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750a2_1_2302:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3267:u32 =
  dsa_R_ESI_32_1_3254:u32 +
  (if dsa_R_DF_1_3258:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3268:u32 =
  dsa_R_EDI_32_1_3259:u32 +
  (if dsa_R_DF_1_3258:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3269:u32 = dsa_R_ECX_32_1_3248:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3269:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp81"*/
label nocjmp81
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07c2, 0, u32, rd
  @context "R_ESI_32" = 0xdce750a6, 0, u32, rd
  @context "R_ECX_32" = 0xc, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750a6]" = 0x41, 167, u8, rd
  @context "mem32[0xdce750a7]" = 0x41, 168, u8, rd
  @context "mem32[0xdce750a8]" = 0x41, 169, u8, rd
  @context "mem32[0xdce750a9]" = 0x41, 170, u8, rd
  @context "mem32[0xffaf07c2]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07c3]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07c4]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07c5]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07c5_1_3270:u8 = low:u8(0:u8)
dsa_mem_ffaf07c2_1_3271:u8 = low:u8(0:u8)
dsa_mem_ffaf07c3_1_3272:u8 = low:u8(0:u8)
dsa_mem_ffaf07c4_1_3273:u8 = low:u8(0:u8)
dsa_R_ZF_1_3274:bool = false
dsa_R_ESI_32_1_3275:u32 = 0xdce750a6:u32
dsa_R_AF_1_3276:bool = false
dsa_R_OF_1_3277:bool = false
dsa_R_SF_1_3278:bool = false
dsa_R_DF_1_3279:bool = false
dsa_R_EDI_32_1_3280:u32 = 0xffaf07c2:u32
dsa_R_CF_1_3281:bool = true
dsa_R_EFLAGS_1_3282:u32 = 0x207:u32
dsa_R_PF_1_3283:bool = true
assert ~(dsa_R_ECX_32_1_3269:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp84"*/
label nocjmp84
dsa_mem_ffaf07c2_1_3284:u8 =
  low:u8(pad:u32(dsa_mem_dce750a9_1_2309:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750a8_1_2308:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750a7_1_2307:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750a6_1_2306:u8))))
dsa_mem_ffaf07c3_1_3285:u8 =
  low:u8((pad:u32(dsa_mem_dce750a9_1_2309:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750a8_1_2308:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750a7_1_2307:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750a6_1_2306:u8)))) >> 8:u32)
dsa_mem_ffaf07c4_1_3286:u8 =
  low:u8((pad:u32(dsa_mem_dce750a9_1_2309:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750a8_1_2308:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750a7_1_2307:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750a6_1_2306:u8)))) >> 0x10:u32)
dsa_mem_ffaf07c5_1_3287:u8 =
  low:u8((pad:u32(dsa_mem_dce750a9_1_2309:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750a8_1_2308:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750a7_1_2307:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750a6_1_2306:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3288:u32 =
  dsa_R_ESI_32_1_3275:u32 +
  (if dsa_R_DF_1_3279:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3289:u32 =
  dsa_R_EDI_32_1_3280:u32 +
  (if dsa_R_DF_1_3279:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3290:u32 = dsa_R_ECX_32_1_3269:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3290:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp83"*/
label nocjmp83
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07c6, 0, u32, rd
  @context "R_ESI_32" = 0xdce750aa, 0, u32, rd
  @context "R_ECX_32" = 0xb, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750aa]" = 0x41, 171, u8, rd
  @context "mem32[0xdce750ab]" = 0x41, 172, u8, rd
  @context "mem32[0xdce750ac]" = 0x41, 173, u8, rd
  @context "mem32[0xdce750ad]" = 0x41, 174, u8, rd
  @context "mem32[0xffaf07c6]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07c7]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07c8]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07c9]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07c6_1_3291:u8 = low:u8(0:u8)
dsa_mem_ffaf07c7_1_3292:u8 = low:u8(0:u8)
dsa_mem_ffaf07c9_1_3293:u8 = low:u8(0:u8)
dsa_mem_ffaf07c8_1_3294:u8 = low:u8(0:u8)
dsa_R_ZF_1_3295:bool = false
dsa_R_ESI_32_1_3296:u32 = 0xdce750aa:u32
dsa_R_AF_1_3297:bool = false
dsa_R_OF_1_3298:bool = false
dsa_R_SF_1_3299:bool = false
dsa_R_DF_1_3300:bool = false
dsa_R_EDI_32_1_3301:u32 = 0xffaf07c6:u32
dsa_R_CF_1_3302:bool = true
dsa_R_EFLAGS_1_3303:u32 = 0x207:u32
dsa_R_PF_1_3304:bool = true
assert ~(dsa_R_ECX_32_1_3290:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp86"*/
label nocjmp86
dsa_mem_ffaf07c6_1_3305:u8 =
  low:u8(pad:u32(dsa_mem_dce750ad_1_2313:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750ac_1_2312:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750ab_1_2311:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750aa_1_2310:u8))))
dsa_mem_ffaf07c7_1_3306:u8 =
  low:u8((pad:u32(dsa_mem_dce750ad_1_2313:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750ac_1_2312:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750ab_1_2311:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750aa_1_2310:u8)))) >> 8:u32)
dsa_mem_ffaf07c8_1_3307:u8 =
  low:u8((pad:u32(dsa_mem_dce750ad_1_2313:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750ac_1_2312:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750ab_1_2311:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750aa_1_2310:u8)))) >> 0x10:u32)
dsa_mem_ffaf07c9_1_3308:u8 =
  low:u8((pad:u32(dsa_mem_dce750ad_1_2313:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750ac_1_2312:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750ab_1_2311:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750aa_1_2310:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3309:u32 =
  dsa_R_ESI_32_1_3296:u32 +
  (if dsa_R_DF_1_3300:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3310:u32 =
  dsa_R_EDI_32_1_3301:u32 +
  (if dsa_R_DF_1_3300:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3311:u32 = dsa_R_ECX_32_1_3290:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3311:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp85"*/
label nocjmp85
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07ca, 0, u32, rd
  @context "R_ESI_32" = 0xdce750ae, 0, u32, rd
  @context "R_ECX_32" = 0xa, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750ae]" = 0x41, 175, u8, rd
  @context "mem32[0xdce750af]" = 0x41, 176, u8, rd
  @context "mem32[0xdce750b0]" = 0x41, 177, u8, rd
  @context "mem32[0xdce750b1]" = 0x41, 178, u8, rd
  @context "mem32[0xffaf07ca]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07cb]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07cc]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07cd]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07cc_1_3312:u8 = low:u8(0:u8)
dsa_mem_ffaf07cb_1_3313:u8 = low:u8(0:u8)
dsa_mem_ffaf07ca_1_3314:u8 = low:u8(0:u8)
dsa_mem_ffaf07cd_1_3315:u8 = low:u8(0:u8)
dsa_R_ZF_1_3316:bool = false
dsa_R_ESI_32_1_3317:u32 = 0xdce750ae:u32
dsa_R_AF_1_3318:bool = false
dsa_R_OF_1_3319:bool = false
dsa_R_SF_1_3320:bool = false
dsa_R_DF_1_3321:bool = false
dsa_R_EDI_32_1_3322:u32 = 0xffaf07ca:u32
dsa_R_CF_1_3323:bool = true
dsa_R_EFLAGS_1_3324:u32 = 0x207:u32
dsa_R_PF_1_3325:bool = true
assert ~(dsa_R_ECX_32_1_3311:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp88"*/
label nocjmp88
dsa_mem_ffaf07ca_1_3326:u8 =
  low:u8(pad:u32(dsa_mem_dce750b1_1_2317:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750b0_1_2316:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750af_1_2315:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ae_1_2314:u8))))
dsa_mem_ffaf07cb_1_3327:u8 =
  low:u8((pad:u32(dsa_mem_dce750b1_1_2317:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750b0_1_2316:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750af_1_2315:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ae_1_2314:u8)))) >> 8:u32)
dsa_mem_ffaf07cc_1_3328:u8 =
  low:u8((pad:u32(dsa_mem_dce750b1_1_2317:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750b0_1_2316:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750af_1_2315:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ae_1_2314:u8)))) >> 0x10:u32)
dsa_mem_ffaf07cd_1_3329:u8 =
  low:u8((pad:u32(dsa_mem_dce750b1_1_2317:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750b0_1_2316:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750af_1_2315:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ae_1_2314:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3330:u32 =
  dsa_R_ESI_32_1_3317:u32 +
  (if dsa_R_DF_1_3321:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3331:u32 =
  dsa_R_EDI_32_1_3322:u32 +
  (if dsa_R_DF_1_3321:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3332:u32 = dsa_R_ECX_32_1_3311:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3332:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp87"*/
label nocjmp87
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07ce, 0, u32, rd
  @context "R_ESI_32" = 0xdce750b2, 0, u32, rd
  @context "R_ECX_32" = 0x9, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750b2]" = 0x41, 179, u8, rd
  @context "mem32[0xdce750b3]" = 0x41, 180, u8, rd
  @context "mem32[0xdce750b4]" = 0x41, 181, u8, rd
  @context "mem32[0xdce750b5]" = 0x41, 182, u8, rd
  @context "mem32[0xffaf07ce]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07cf]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07d0]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07d1]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07d0_1_3333:u8 = low:u8(0:u8)
dsa_mem_ffaf07ce_1_3334:u8 = low:u8(0:u8)
dsa_mem_ffaf07cf_1_3335:u8 = low:u8(0:u8)
dsa_mem_ffaf07d1_1_3336:u8 = low:u8(0:u8)
dsa_R_ZF_1_3337:bool = false
dsa_R_ESI_32_1_3338:u32 = 0xdce750b2:u32
dsa_R_AF_1_3339:bool = false
dsa_R_OF_1_3340:bool = false
dsa_R_SF_1_3341:bool = false
dsa_R_DF_1_3342:bool = false
dsa_R_EDI_32_1_3343:u32 = 0xffaf07ce:u32
dsa_R_CF_1_3344:bool = true
dsa_R_EFLAGS_1_3345:u32 = 0x207:u32
dsa_R_PF_1_3346:bool = true
assert ~(dsa_R_ECX_32_1_3332:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp90"*/
label nocjmp90
dsa_mem_ffaf07ce_1_3347:u8 =
  low:u8(pad:u32(dsa_mem_dce750b5_1_2321:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750b4_1_2320:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750b3_1_2319:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750b2_1_2318:u8))))
dsa_mem_ffaf07cf_1_3348:u8 =
  low:u8((pad:u32(dsa_mem_dce750b5_1_2321:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750b4_1_2320:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750b3_1_2319:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750b2_1_2318:u8)))) >> 8:u32)
dsa_mem_ffaf07d0_1_3349:u8 =
  low:u8((pad:u32(dsa_mem_dce750b5_1_2321:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750b4_1_2320:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750b3_1_2319:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750b2_1_2318:u8)))) >> 0x10:u32)
dsa_mem_ffaf07d1_1_3350:u8 =
  low:u8((pad:u32(dsa_mem_dce750b5_1_2321:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750b4_1_2320:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750b3_1_2319:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750b2_1_2318:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3351:u32 =
  dsa_R_ESI_32_1_3338:u32 +
  (if dsa_R_DF_1_3342:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3352:u32 =
  dsa_R_EDI_32_1_3343:u32 +
  (if dsa_R_DF_1_3342:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3353:u32 = dsa_R_ECX_32_1_3332:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3353:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp89"*/
label nocjmp89
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07d2, 0, u32, rd
  @context "R_ESI_32" = 0xdce750b6, 0, u32, rd
  @context "R_ECX_32" = 0x8, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750b6]" = 0x41, 183, u8, rd
  @context "mem32[0xdce750b7]" = 0x41, 184, u8, rd
  @context "mem32[0xdce750b8]" = 0x41, 185, u8, rd
  @context "mem32[0xdce750b9]" = 0x41, 186, u8, rd
  @context "mem32[0xffaf07d2]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07d3]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07d4]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07d5]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07d3_1_3354:u8 = low:u8(0:u8)
dsa_mem_ffaf07d2_1_3355:u8 = low:u8(0:u8)
dsa_mem_ffaf07d4_1_3356:u8 = low:u8(0:u8)
dsa_mem_ffaf07d5_1_3357:u8 = low:u8(0:u8)
dsa_R_ZF_1_3358:bool = false
dsa_R_ESI_32_1_3359:u32 = 0xdce750b6:u32
dsa_R_AF_1_3360:bool = false
dsa_R_OF_1_3361:bool = false
dsa_R_SF_1_3362:bool = false
dsa_R_DF_1_3363:bool = false
dsa_R_EDI_32_1_3364:u32 = 0xffaf07d2:u32
dsa_R_CF_1_3365:bool = true
dsa_R_EFLAGS_1_3366:u32 = 0x207:u32
dsa_R_PF_1_3367:bool = true
assert ~(dsa_R_ECX_32_1_3353:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp92"*/
label nocjmp92
dsa_mem_ffaf07d2_1_3368:u8 =
  low:u8(pad:u32(dsa_mem_dce750b9_1_2325:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750b8_1_2324:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750b7_1_2323:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750b6_1_2322:u8))))
dsa_mem_ffaf07d3_1_3369:u8 =
  low:u8((pad:u32(dsa_mem_dce750b9_1_2325:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750b8_1_2324:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750b7_1_2323:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750b6_1_2322:u8)))) >> 8:u32)
dsa_mem_ffaf07d4_1_3370:u8 =
  low:u8((pad:u32(dsa_mem_dce750b9_1_2325:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750b8_1_2324:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750b7_1_2323:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750b6_1_2322:u8)))) >> 0x10:u32)
dsa_mem_ffaf07d5_1_3371:u8 =
  low:u8((pad:u32(dsa_mem_dce750b9_1_2325:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750b8_1_2324:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750b7_1_2323:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750b6_1_2322:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3372:u32 =
  dsa_R_ESI_32_1_3359:u32 +
  (if dsa_R_DF_1_3363:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3373:u32 =
  dsa_R_EDI_32_1_3364:u32 +
  (if dsa_R_DF_1_3363:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3374:u32 = dsa_R_ECX_32_1_3353:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3374:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp91"*/
label nocjmp91
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07d6, 0, u32, rd
  @context "R_ESI_32" = 0xdce750ba, 0, u32, rd
  @context "R_ECX_32" = 0x7, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750ba]" = 0x41, 187, u8, rd
  @context "mem32[0xdce750bb]" = 0x41, 188, u8, rd
  @context "mem32[0xdce750bc]" = 0x41, 189, u8, rd
  @context "mem32[0xdce750bd]" = 0x41, 190, u8, rd
  @context "mem32[0xffaf07d6]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07d7]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07d8]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07d9]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07d8_1_3375:u8 = low:u8(0:u8)
dsa_mem_ffaf07d6_1_3376:u8 = low:u8(0:u8)
dsa_mem_ffaf07d7_1_3377:u8 = low:u8(0:u8)
dsa_mem_ffaf07d9_1_3378:u8 = low:u8(0:u8)
dsa_R_ZF_1_3379:bool = false
dsa_R_ESI_32_1_3380:u32 = 0xdce750ba:u32
dsa_R_AF_1_3381:bool = false
dsa_R_OF_1_3382:bool = false
dsa_R_SF_1_3383:bool = false
dsa_R_DF_1_3384:bool = false
dsa_R_EDI_32_1_3385:u32 = 0xffaf07d6:u32
dsa_R_CF_1_3386:bool = true
dsa_R_EFLAGS_1_3387:u32 = 0x207:u32
dsa_R_PF_1_3388:bool = true
assert ~(dsa_R_ECX_32_1_3374:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp94"*/
label nocjmp94
dsa_mem_ffaf07d6_1_3389:u8 =
  low:u8(pad:u32(dsa_mem_dce750bd_1_2329:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750bc_1_2328:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750bb_1_2327:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ba_1_2326:u8))))
dsa_mem_ffaf07d7_1_3390:u8 =
  low:u8((pad:u32(dsa_mem_dce750bd_1_2329:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750bc_1_2328:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750bb_1_2327:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ba_1_2326:u8)))) >> 8:u32)
dsa_mem_ffaf07d8_1_3391:u8 =
  low:u8((pad:u32(dsa_mem_dce750bd_1_2329:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750bc_1_2328:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750bb_1_2327:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ba_1_2326:u8)))) >> 0x10:u32)
dsa_mem_ffaf07d9_1_3392:u8 =
  low:u8((pad:u32(dsa_mem_dce750bd_1_2329:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750bc_1_2328:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750bb_1_2327:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ba_1_2326:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3393:u32 =
  dsa_R_ESI_32_1_3380:u32 +
  (if dsa_R_DF_1_3384:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3394:u32 =
  dsa_R_EDI_32_1_3385:u32 +
  (if dsa_R_DF_1_3384:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3395:u32 = dsa_R_ECX_32_1_3374:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3395:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp93"*/
label nocjmp93
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07da, 0, u32, rd
  @context "R_ESI_32" = 0xdce750be, 0, u32, rd
  @context "R_ECX_32" = 0x6, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750be]" = 0x41, 191, u8, rd
  @context "mem32[0xdce750bf]" = 0x41, 192, u8, rd
  @context "mem32[0xdce750c0]" = 0x41, 193, u8, rd
  @context "mem32[0xdce750c1]" = 0x41, 194, u8, rd
  @context "mem32[0xffaf07da]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07db]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07dc]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07dd]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07dc_1_3396:u8 = low:u8(0:u8)
dsa_mem_ffaf07dd_1_3397:u8 = low:u8(0:u8)
dsa_mem_ffaf07da_1_3398:u8 = low:u8(0:u8)
dsa_mem_ffaf07db_1_3399:u8 = low:u8(0:u8)
dsa_R_ZF_1_3400:bool = false
dsa_R_ESI_32_1_3401:u32 = 0xdce750be:u32
dsa_R_AF_1_3402:bool = false
dsa_R_OF_1_3403:bool = false
dsa_R_SF_1_3404:bool = false
dsa_R_DF_1_3405:bool = false
dsa_R_EDI_32_1_3406:u32 = 0xffaf07da:u32
dsa_R_CF_1_3407:bool = true
dsa_R_EFLAGS_1_3408:u32 = 0x207:u32
dsa_R_PF_1_3409:bool = true
assert ~(dsa_R_ECX_32_1_3395:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp96"*/
label nocjmp96
dsa_mem_ffaf07da_1_3410:u8 =
  low:u8(pad:u32(dsa_mem_dce750c1_1_2333:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750c0_1_2332:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750bf_1_2331:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750be_1_2330:u8))))
dsa_mem_ffaf07db_1_3411:u8 =
  low:u8((pad:u32(dsa_mem_dce750c1_1_2333:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750c0_1_2332:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750bf_1_2331:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750be_1_2330:u8)))) >> 8:u32)
dsa_mem_ffaf07dc_1_3412:u8 =
  low:u8((pad:u32(dsa_mem_dce750c1_1_2333:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750c0_1_2332:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750bf_1_2331:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750be_1_2330:u8)))) >> 0x10:u32)
dsa_mem_ffaf07dd_1_3413:u8 =
  low:u8((pad:u32(dsa_mem_dce750c1_1_2333:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750c0_1_2332:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750bf_1_2331:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750be_1_2330:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3414:u32 =
  dsa_R_ESI_32_1_3401:u32 +
  (if dsa_R_DF_1_3405:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3415:u32 =
  dsa_R_EDI_32_1_3406:u32 +
  (if dsa_R_DF_1_3405:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3416:u32 = dsa_R_ECX_32_1_3395:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3416:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp95"*/
label nocjmp95
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07de, 0, u32, rd
  @context "R_ESI_32" = 0xdce750c2, 0, u32, rd
  @context "R_ECX_32" = 0x5, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750c2]" = 0x41, 195, u8, rd
  @context "mem32[0xdce750c3]" = 0x41, 196, u8, rd
  @context "mem32[0xdce750c4]" = 0x41, 197, u8, rd
  @context "mem32[0xdce750c5]" = 0x41, 198, u8, rd
  @context "mem32[0xffaf07de]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07df]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07e0]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07e1]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07e1_1_3417:u8 = low:u8(0:u8)
dsa_mem_ffaf07e0_1_3418:u8 = low:u8(0:u8)
dsa_mem_ffaf07de_1_3419:u8 = low:u8(0:u8)
dsa_mem_ffaf07df_1_3420:u8 = low:u8(0:u8)
dsa_R_ZF_1_3421:bool = false
dsa_R_ESI_32_1_3422:u32 = 0xdce750c2:u32
dsa_R_AF_1_3423:bool = false
dsa_R_OF_1_3424:bool = false
dsa_R_SF_1_3425:bool = false
dsa_R_DF_1_3426:bool = false
dsa_R_EDI_32_1_3427:u32 = 0xffaf07de:u32
dsa_R_CF_1_3428:bool = true
dsa_R_EFLAGS_1_3429:u32 = 0x207:u32
dsa_R_PF_1_3430:bool = true
assert ~(dsa_R_ECX_32_1_3416:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp98"*/
label nocjmp98
dsa_mem_ffaf07de_1_3431:u8 =
  low:u8(pad:u32(dsa_mem_dce750c5_1_2337:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750c4_1_2336:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750c3_1_2335:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750c2_1_2334:u8))))
dsa_mem_ffaf07df_1_3432:u8 =
  low:u8((pad:u32(dsa_mem_dce750c5_1_2337:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750c4_1_2336:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750c3_1_2335:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750c2_1_2334:u8)))) >> 8:u32)
dsa_mem_ffaf07e0_1_3433:u8 =
  low:u8((pad:u32(dsa_mem_dce750c5_1_2337:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750c4_1_2336:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750c3_1_2335:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750c2_1_2334:u8)))) >> 0x10:u32)
dsa_mem_ffaf07e1_1_3434:u8 =
  low:u8((pad:u32(dsa_mem_dce750c5_1_2337:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750c4_1_2336:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750c3_1_2335:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750c2_1_2334:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3435:u32 =
  dsa_R_ESI_32_1_3422:u32 +
  (if dsa_R_DF_1_3426:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3436:u32 =
  dsa_R_EDI_32_1_3427:u32 +
  (if dsa_R_DF_1_3426:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3437:u32 = dsa_R_ECX_32_1_3416:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3437:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp97"*/
label nocjmp97
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07e2, 0, u32, rd
  @context "R_ESI_32" = 0xdce750c6, 0, u32, rd
  @context "R_ECX_32" = 0x4, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750c6]" = 0x41, 199, u8, rd
  @context "mem32[0xdce750c7]" = 0x41, 200, u8, rd
  @context "mem32[0xdce750c8]" = 0x41, 201, u8, rd
  @context "mem32[0xdce750c9]" = 0x41, 202, u8, rd
  @context "mem32[0xffaf07e2]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07e3]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07e4]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07e5]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07e5_1_3438:u8 = low:u8(0:u8)
dsa_mem_ffaf07e3_1_3439:u8 = low:u8(0:u8)
dsa_mem_ffaf07e4_1_3440:u8 = low:u8(0:u8)
dsa_mem_ffaf07e2_1_3441:u8 = low:u8(0:u8)
dsa_R_ZF_1_3442:bool = false
dsa_R_ESI_32_1_3443:u32 = 0xdce750c6:u32
dsa_R_AF_1_3444:bool = false
dsa_R_OF_1_3445:bool = false
dsa_R_SF_1_3446:bool = false
dsa_R_DF_1_3447:bool = false
dsa_R_EDI_32_1_3448:u32 = 0xffaf07e2:u32
dsa_R_CF_1_3449:bool = true
dsa_R_EFLAGS_1_3450:u32 = 0x207:u32
dsa_R_PF_1_3451:bool = true
assert ~(dsa_R_ECX_32_1_3437:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp100"*/
label nocjmp100
dsa_mem_ffaf07e2_1_3452:u8 =
  low:u8(pad:u32(dsa_mem_dce750c9_1_2341:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750c8_1_2340:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750c7_1_2339:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750c6_1_2338:u8))))
dsa_mem_ffaf07e3_1_3453:u8 =
  low:u8((pad:u32(dsa_mem_dce750c9_1_2341:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750c8_1_2340:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750c7_1_2339:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750c6_1_2338:u8)))) >> 8:u32)
dsa_mem_ffaf07e4_1_3454:u8 =
  low:u8((pad:u32(dsa_mem_dce750c9_1_2341:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750c8_1_2340:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750c7_1_2339:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750c6_1_2338:u8)))) >> 0x10:u32)
dsa_mem_ffaf07e5_1_3455:u8 =
  low:u8((pad:u32(dsa_mem_dce750c9_1_2341:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750c8_1_2340:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750c7_1_2339:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750c6_1_2338:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3456:u32 =
  dsa_R_ESI_32_1_3443:u32 +
  (if dsa_R_DF_1_3447:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3457:u32 =
  dsa_R_EDI_32_1_3448:u32 +
  (if dsa_R_DF_1_3447:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3458:u32 = dsa_R_ECX_32_1_3437:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3458:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp99"*/
label nocjmp99
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07e6, 0, u32, rd
  @context "R_ESI_32" = 0xdce750ca, 0, u32, rd
  @context "R_ECX_32" = 0x3, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750ca]" = 0x41, 203, u8, rd
  @context "mem32[0xdce750cb]" = 0x41, 204, u8, rd
  @context "mem32[0xdce750cc]" = 0x41, 205, u8, rd
  @context "mem32[0xdce750cd]" = 0x41, 206, u8, rd
  @context "mem32[0xffaf07e6]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07e7]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07e8]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07e9]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07e7_1_3459:u8 = low:u8(0:u8)
dsa_mem_ffaf07e8_1_3460:u8 = low:u8(0:u8)
dsa_mem_ffaf07e6_1_3461:u8 = low:u8(0:u8)
dsa_mem_ffaf07e9_1_3462:u8 = low:u8(0:u8)
dsa_R_ZF_1_3463:bool = false
dsa_R_ESI_32_1_3464:u32 = 0xdce750ca:u32
dsa_R_AF_1_3465:bool = false
dsa_R_OF_1_3466:bool = false
dsa_R_SF_1_3467:bool = false
dsa_R_DF_1_3468:bool = false
dsa_R_EDI_32_1_3469:u32 = 0xffaf07e6:u32
dsa_R_CF_1_3470:bool = true
dsa_R_EFLAGS_1_3471:u32 = 0x207:u32
dsa_R_PF_1_3472:bool = true
assert ~(dsa_R_ECX_32_1_3458:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp102"*/
label nocjmp102
dsa_mem_ffaf07e6_1_3473:u8 =
  low:u8(pad:u32(dsa_mem_dce750cd_1_2345:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750cc_1_2344:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750cb_1_2343:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ca_1_2342:u8))))
dsa_mem_ffaf07e7_1_3474:u8 =
  low:u8((pad:u32(dsa_mem_dce750cd_1_2345:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750cc_1_2344:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750cb_1_2343:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ca_1_2342:u8)))) >> 8:u32)
dsa_mem_ffaf07e8_1_3475:u8 =
  low:u8((pad:u32(dsa_mem_dce750cd_1_2345:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750cc_1_2344:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750cb_1_2343:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ca_1_2342:u8)))) >> 0x10:u32)
dsa_mem_ffaf07e9_1_3476:u8 =
  low:u8((pad:u32(dsa_mem_dce750cd_1_2345:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750cc_1_2344:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750cb_1_2343:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ca_1_2342:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3477:u32 =
  dsa_R_ESI_32_1_3464:u32 +
  (if dsa_R_DF_1_3468:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3478:u32 =
  dsa_R_EDI_32_1_3469:u32 +
  (if dsa_R_DF_1_3468:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3479:u32 = dsa_R_ECX_32_1_3458:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3479:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp101"*/
label nocjmp101
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07ea, 0, u32, rd
  @context "R_ESI_32" = 0xdce750ce, 0, u32, rd
  @context "R_ECX_32" = 0x2, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750ce]" = 0x41, 207, u8, rd
  @context "mem32[0xdce750cf]" = 0x41, 208, u8, rd
  @context "mem32[0xdce750d0]" = 0x41, 209, u8, rd
  @context "mem32[0xdce750d1]" = 0x41, 210, u8, rd
  @context "mem32[0xffaf07ea]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07eb]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07ec]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07ed]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07eb_1_3480:u8 = low:u8(0:u8)
dsa_mem_ffaf07ed_1_3481:u8 = low:u8(0:u8)
dsa_mem_ffaf07ec_1_3482:u8 = low:u8(0:u8)
dsa_mem_ffaf07ea_1_3483:u8 = low:u8(0:u8)
dsa_R_ZF_1_3484:bool = false
dsa_R_ESI_32_1_3485:u32 = 0xdce750ce:u32
dsa_R_AF_1_3486:bool = false
dsa_R_OF_1_3487:bool = false
dsa_R_SF_1_3488:bool = false
dsa_R_DF_1_3489:bool = false
dsa_R_EDI_32_1_3490:u32 = 0xffaf07ea:u32
dsa_R_CF_1_3491:bool = true
dsa_R_EFLAGS_1_3492:u32 = 0x207:u32
dsa_R_PF_1_3493:bool = true
assert ~(dsa_R_ECX_32_1_3479:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp104"*/
label nocjmp104
dsa_mem_ffaf07ea_1_3494:u8 =
  low:u8(pad:u32(dsa_mem_dce750d1_1_2349:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750d0_1_2348:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750cf_1_2347:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ce_1_2346:u8))))
dsa_mem_ffaf07eb_1_3495:u8 =
  low:u8((pad:u32(dsa_mem_dce750d1_1_2349:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750d0_1_2348:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750cf_1_2347:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ce_1_2346:u8)))) >> 8:u32)
dsa_mem_ffaf07ec_1_3496:u8 =
  low:u8((pad:u32(dsa_mem_dce750d1_1_2349:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750d0_1_2348:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750cf_1_2347:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ce_1_2346:u8)))) >> 0x10:u32)
dsa_mem_ffaf07ed_1_3497:u8 =
  low:u8((pad:u32(dsa_mem_dce750d1_1_2349:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750d0_1_2348:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750cf_1_2347:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750ce_1_2346:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3498:u32 =
  dsa_R_ESI_32_1_3485:u32 +
  (if dsa_R_DF_1_3489:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3499:u32 =
  dsa_R_EDI_32_1_3490:u32 +
  (if dsa_R_DF_1_3489:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3500:u32 = dsa_R_ECX_32_1_3479:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_3500:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp103"*/
label nocjmp103
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xffaf07ee, 0, u32, rd
  @context "R_ESI_32" = 0xdce750d2, 0, u32, rd
  @context "R_ECX_32" = 0x1, -1, u32, rw
  @context "R_EFLAGS" = 0x207, 0, u32, rd
  @context "mem32[0xdce750d2]" = 0x41, 211, u8, rd
  @context "mem32[0xdce750d3]" = 0x41, 212, u8, rd
  @context "mem32[0xdce750d4]" = 0x41, 213, u8, rd
  @context "mem32[0xdce750d5]" = 0xa, 214, u8, rd
  @context "mem32[0xffaf07ee]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07ef]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07f0]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf07f1]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_ffaf07ef_1_3501:u8 = low:u8(0:u8)
dsa_mem_ffaf07f0_1_3502:u8 = low:u8(0:u8)
dsa_mem_ffaf07ee_1_3503:u8 = low:u8(0:u8)
dsa_mem_ffaf07f1_1_3504:u8 = low:u8(0:u8)
dsa_R_ZF_1_3505:bool = false
dsa_R_ESI_32_1_3506:u32 = 0xdce750d2:u32
dsa_R_AF_1_3507:bool = false
dsa_R_OF_1_3508:bool = false
dsa_R_SF_1_3509:bool = false
dsa_R_DF_1_3510:bool = false
dsa_R_EDI_32_1_3511:u32 = 0xffaf07ee:u32
dsa_R_CF_1_3512:bool = true
dsa_R_EFLAGS_1_3513:u32 = 0x207:u32
dsa_R_PF_1_3514:bool = true
assert ~(dsa_R_ECX_32_1_3500:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp106"*/
label nocjmp106
dsa_mem_ffaf07ee_1_3515:u8 =
  low:u8(pad:u32(dsa_mem_dce750d5_1_2353:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750d4_1_2352:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750d3_1_2351:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750d2_1_2350:u8))))
dsa_mem_ffaf07ef_1_3516:u8 =
  low:u8((pad:u32(dsa_mem_dce750d5_1_2353:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750d4_1_2352:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750d3_1_2351:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750d2_1_2350:u8)))) >> 8:u32)
dsa_mem_ffaf07f0_1_3517:u8 =
  low:u8((pad:u32(dsa_mem_dce750d5_1_2353:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750d4_1_2352:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750d3_1_2351:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750d2_1_2350:u8)))) >> 0x10:u32)
dsa_mem_ffaf07f1_1_3518:u8 =
  low:u8((pad:u32(dsa_mem_dce750d5_1_2353:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_dce750d4_1_2352:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_dce750d3_1_2351:u8) << 8:u32 |
         pad:u32(dsa_mem_dce750d2_1_2350:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_3519:u32 =
  dsa_R_ESI_32_1_3506:u32 +
  (if dsa_R_DF_1_3510:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_3520:u32 =
  dsa_R_EDI_32_1_3511:u32 +
  (if dsa_R_DF_1_3510:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_3521:u32 = dsa_R_ECX_32_1_3500:u32 - 1:u32
assert dsa_R_ECX_32_1_3521:u32 == 0:u32
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp105"*/
addr 0xdcf2eef0 @asm "mov    ecx,DWORD PTR [ebp+0x20]" @tid "0"
  @context "R_ECX_32" = 0x0, -1, u32, wr
  @context "R_EBP_32" = 0x8656008, 0, u32, rd
  @context "mem32[0x8656028]" = 0x0, 0, u8, rd
  @context "mem32[0x8656029]" = 0x60, 0, u8, rd
  @context "mem32[0x865602a]" = 0xe7, 0, u8, rd
  @context "mem32[0x865602b]" = 0xdc, 0, u8, rd
label pc_0xdcf2eef0
dsa_mem_865602b_1_3522:u8 = low:u8(0xdc:u8)
dsa_mem_865602a_1_3523:u8 = low:u8(0xe7:u8)
dsa_mem_8656028_1_3524:u8 = low:u8(0:u8)
dsa_mem_8656029_1_3525:u8 = low:u8(0x60:u8)
dsa_R_EBP_32_1_3526:u32 = 0x8656008:u32
dsa_R_ECX_32_1_3527:u32 =
  pad:u32(dsa_mem_865602b_1_3522:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_865602a_1_3523:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_8656029_1_3525:u8) << 8:u32 |
  pad:u32(dsa_mem_8656028_1_3524:u8)))
addr 0xdd0042f0 @asm "mov    bl,BYTE PTR [eax]" @tid "0"
  @context "R_EBX_32" = 0xdd06d000, 0, u32, wr
  @context "R_EAX_32" = 0xffaf071c, 0, u32, rd
  @context "mem32[0xffaf071c]" = 0x41, -1, u8, rd
label pc_0xdd0042f0
dsa_R_EBX_32_1_3528:u32 = 0xdd06d000:u32
dsa_R_EAX_32_1_3529:u32 = 0xffaf071c:u32
dsa_R_EBX_32_1_3530:u32 =
  concat:[extract:31:8:[dsa_R_EBX_32_1_3528:u32]][
   pad:u8(dsa_mem_ffaf071c_1_2404:u8)]
addr 0xdd0042f2 @asm "cmp    bl,BYTE PTR [edx]" @tid "0"
  @context "R_EBX_32" = 0xdd06d041, -1, u32, rd
  @context "R_EDX_32" = 0x8048cde, 0, u32, rd
  @context "R_EFLAGS" = 0x297, 0, u32, wr
  @context "mem32[0x8048cde]" = 0x41, 0, u8, rd
label pc_0xdd0042f2
dsa_mem_8048cde_1_3531:u8 = low:u8(0x41:u8)
dsa_R_ZF_1_3532:bool = false
dsa_R_AF_1_3533:bool = true
dsa_R_OF_1_3534:bool = false
dsa_R_SF_1_3535:bool = true
dsa_R_DF_1_3536:bool = false
dsa_R_EDX_32_1_3537:u32 = 0x8048cde:u32
dsa_R_CF_1_3538:bool = true
dsa_R_EFLAGS_1_3539:u32 = 0x297:u32
dsa_R_PF_1_3540:bool = true
dsa_T_t_1_3541:u8 =
  low:u8(dsa_R_EBX_32_1_3530:u32) - pad:u8(dsa_mem_8048cde_1_3531:u8)
dsa_R_CF_1_3542:bool =
  low:u8(dsa_R_EBX_32_1_3530:u32) < pad:u8(dsa_mem_8048cde_1_3531:u8)
dsa_R_OF_1_3543:bool =
  high:bool((low:u8(dsa_R_EBX_32_1_3530:u32) ^
            pad:u8(dsa_mem_8048cde_1_3531:u8)) &
            (low:u8(dsa_R_EBX_32_1_3530:u32) ^ dsa_T_t_1_3541:u8))
dsa_R_AF_1_3544:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_3541:u8 ^ low:u8(dsa_R_EBX_32_1_3530:u32) ^
  pad:u8(dsa_mem_8048cde_1_3531:u8)))
dsa_R_PF_3_3547:bool =
  ~low:bool(let dsa_T_acc_1_3545:u8 :=
                                        dsa_T_t_1_3541:u8 >> 4:u8 ^
                                        dsa_T_t_1_3541:u8 in
            let dsa_T_acc_2_3546:u8 :=
                                        dsa_T_acc_1_3545:u8 >> 2:u8 ^
                                        dsa_T_acc_1_3545:u8 in
            dsa_T_acc_2_3546:u8 >> 1:u8 ^ dsa_T_acc_2_3546:u8)
dsa_R_SF_1_3548:bool = high:bool(dsa_T_t_1_3541:u8)
dsa_R_ZF_1_3549:bool = 0:u8 == dsa_T_t_1_3541:u8
addr 0xdd0042f4 @asm "jne    0x00000000dd00433f" @tid "0"
  @context "R_EIP" = 0xdd0042f4, 0, u32, rw
  @context "R_EFLAGS" = 0x246, -1, u32, rd
label pc_0xdd0042f4
dsa_R_DF_1_3550:bool = false
dsa_R_EIP_1_3551:u32 = 0xdd0042f4:u32
assert ~~dsa_R_ZF_1_3549:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdd00433f:u32, "nocjmp107"*/
label nocjmp107
addr 0xdd0042f6 @asm "mov    bl,BYTE PTR [eax+0x1]" @tid "0"
  @context "R_EBX_32" = 0xdd06d041, -1, u32, wr
  @context "R_EAX_32" = 0xffaf071c, 0, u32, rd
  @context "mem32[0xffaf071d]" = 0x41, -1, u8, rd
label pc_0xdd0042f6
dsa_R_EAX_32_1_3552:u32 = 0xffaf071c:u32
dsa_R_EBX_32_1_3553:u32 =
  concat:[extract:31:8:[dsa_R_EBX_32_1_3530:u32]][
   pad:u8(dsa_mem_ffaf071d_1_2405:u8)]
addr 0xdd0042f9 @asm "cmp    bl,BYTE PTR [edx+0x1]" @tid "0"
  @context "R_EBX_32" = 0xdd06d041, -1, u32, rd
  @context "R_EDX_32" = 0x8048cde, 0, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
  @context "mem32[0x8048cdf]" = 0x41, 0, u8, rd
label pc_0xdd0042f9
dsa_mem_8048cdf_1_3554:u8 = low:u8(0x41:u8)
dsa_R_DF_1_3555:bool = false
dsa_R_EDX_32_1_3556:u32 = 0x8048cde:u32
dsa_T_t_1_3557:u8 =
  low:u8(dsa_R_EBX_32_1_3553:u32) - pad:u8(dsa_mem_8048cdf_1_3554:u8)
dsa_R_CF_1_3558:bool =
  low:u8(dsa_R_EBX_32_1_3553:u32) < pad:u8(dsa_mem_8048cdf_1_3554:u8)
dsa_R_OF_1_3559:bool =
  high:bool((low:u8(dsa_R_EBX_32_1_3553:u32) ^
            pad:u8(dsa_mem_8048cdf_1_3554:u8)) &
            (low:u8(dsa_R_EBX_32_1_3553:u32) ^ dsa_T_t_1_3557:u8))
dsa_R_AF_1_3560:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_3557:u8 ^ low:u8(dsa_R_EBX_32_1_3553:u32) ^
  pad:u8(dsa_mem_8048cdf_1_3554:u8)))
dsa_R_PF_3_3563:bool =
  ~low:bool(let dsa_T_acc_1_3561:u8 :=
                                        dsa_T_t_1_3557:u8 >> 4:u8 ^
                                        dsa_T_t_1_3557:u8 in
            let dsa_T_acc_2_3562:u8 :=
                                        dsa_T_acc_1_3561:u8 >> 2:u8 ^
                                        dsa_T_acc_1_3561:u8 in
            dsa_T_acc_2_3562:u8 >> 1:u8 ^ dsa_T_acc_2_3562:u8)
dsa_R_SF_1_3564:bool = high:bool(dsa_T_t_1_3557:u8)
dsa_R_ZF_1_3565:bool = 0:u8 == dsa_T_t_1_3557:u8
addr 0xdd0042fc @asm "jne    0x00000000dd00433f" @tid "0"
  @context "R_EIP" = 0xdd0042fc, 0, u32, rw
  @context "R_EFLAGS" = 0x246, -1, u32, rd
label pc_0xdd0042fc
dsa_R_DF_1_3566:bool = false
dsa_R_EIP_1_3567:u32 = 0xdd0042fc:u32
assert ~~dsa_R_ZF_1_3565:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdd00433f:u32, "nocjmp108"*/
label nocjmp108
addr 0xdd0042fe @asm "cmp    ecx,0x2" @tid "0"
  @context "R_ECX_32" = 0x4, 0, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
label pc_0xdd0042fe
dsa_R_ECX_32_1_3568:u32 = 4:u32
dsa_R_DF_1_3569:bool = false
dsa_T_t_1_3570:u32 = dsa_R_ECX_32_1_3568:u32 - 2:u32
dsa_R_CF_1_3571:bool = dsa_R_ECX_32_1_3568:u32 < 2:u32
dsa_R_OF_1_3572:bool =
  high:bool((dsa_R_ECX_32_1_3568:u32 ^ 2:u32) &
            (dsa_R_ECX_32_1_3568:u32 ^ dsa_T_t_1_3570:u32))
dsa_R_AF_1_3573:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_T_t_1_3570:u32 ^ dsa_R_ECX_32_1_3568:u32 ^ 2:u32))
dsa_R_PF_3_3576:bool =
  ~low:bool(let dsa_T_acc_1_3574:u32 :=
                                         dsa_T_t_1_3570:u32 >> 4:u32 ^
                                         dsa_T_t_1_3570:u32 in
            let dsa_T_acc_2_3575:u32 :=
                                         dsa_T_acc_1_3574:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3574:u32 in
            dsa_T_acc_2_3575:u32 >> 1:u32 ^ dsa_T_acc_2_3575:u32)
dsa_R_SF_1_3577:bool = high:bool(dsa_T_t_1_3570:u32)
dsa_R_ZF_1_3578:bool = 0:u32 == dsa_T_t_1_3570:u32
addr 0xdd004303 @asm "mov    bl,BYTE PTR [eax+0x2]" @tid "0"
  @context "R_EBX_32" = 0xdd06d041, -1, u32, wr
  @context "R_EAX_32" = 0xffaf071c, 0, u32, rd
  @context "mem32[0xffaf071e]" = 0x41, -1, u8, rd
label pc_0xdd004303
dsa_R_EAX_32_1_3579:u32 = 0xffaf071c:u32
dsa_R_EBX_32_1_3580:u32 =
  concat:[extract:31:8:[dsa_R_EBX_32_1_3553:u32]][
   pad:u8(dsa_mem_ffaf071e_1_2423:u8)]
addr 0xdd004306 @asm "cmp    bl,BYTE PTR [edx+0x2]" @tid "0"
  @context "R_EBX_32" = 0xdd06d041, -1, u32, rd
  @context "R_EDX_32" = 0x8048cde, 0, u32, rd
  @context "R_EFLAGS" = 0x202, 0, u32, wr
  @context "mem32[0x8048ce0]" = 0x41, 0, u8, rd
label pc_0xdd004306
dsa_mem_8048ce0_1_3581:u8 = low:u8(0x41:u8)
dsa_R_ZF_1_3582:bool = false
dsa_R_AF_1_3583:bool = false
dsa_R_OF_1_3584:bool = false
dsa_R_SF_1_3585:bool = false
dsa_R_DF_1_3586:bool = false
dsa_R_EDX_32_1_3587:u32 = 0x8048cde:u32
dsa_R_CF_1_3588:bool = false
dsa_R_EFLAGS_1_3589:u32 = 0x202:u32
dsa_R_PF_1_3590:bool = false
dsa_T_t_1_3591:u8 =
  low:u8(dsa_R_EBX_32_1_3580:u32) - pad:u8(dsa_mem_8048ce0_1_3581:u8)
dsa_R_CF_1_3592:bool =
  low:u8(dsa_R_EBX_32_1_3580:u32) < pad:u8(dsa_mem_8048ce0_1_3581:u8)
dsa_R_OF_1_3593:bool =
  high:bool((low:u8(dsa_R_EBX_32_1_3580:u32) ^
            pad:u8(dsa_mem_8048ce0_1_3581:u8)) &
            (low:u8(dsa_R_EBX_32_1_3580:u32) ^ dsa_T_t_1_3591:u8))
dsa_R_AF_1_3594:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_3591:u8 ^ low:u8(dsa_R_EBX_32_1_3580:u32) ^
  pad:u8(dsa_mem_8048ce0_1_3581:u8)))
dsa_R_PF_3_3597:bool =
  ~low:bool(let dsa_T_acc_1_3595:u8 :=
                                        dsa_T_t_1_3591:u8 >> 4:u8 ^
                                        dsa_T_t_1_3591:u8 in
            let dsa_T_acc_2_3596:u8 :=
                                        dsa_T_acc_1_3595:u8 >> 2:u8 ^
                                        dsa_T_acc_1_3595:u8 in
            dsa_T_acc_2_3596:u8 >> 1:u8 ^ dsa_T_acc_2_3596:u8)
dsa_R_SF_1_3598:bool = high:bool(dsa_T_t_1_3591:u8)
dsa_R_ZF_1_3599:bool = 0:u8 == dsa_T_t_1_3591:u8
addr 0xdd004309 @asm "jne    0x00000000dd00433f" @tid "0"
  @context "R_EIP" = 0xdd004309, 0, u32, rw
  @context "R_EFLAGS" = 0x246, -1, u32, rd
label pc_0xdd004309
dsa_R_DF_1_3600:bool = false
dsa_R_EIP_1_3601:u32 = 0xdd004309:u32
assert ~~dsa_R_ZF_1_3599:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdd00433f:u32, "nocjmp109"*/
label nocjmp109
addr 0xdd00430b @asm "cmp    ecx,0x3" @tid "0"
  @context "R_ECX_32" = 0x4, 0, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
label pc_0xdd00430b
dsa_R_ECX_32_1_3602:u32 = 4:u32
dsa_R_DF_1_3603:bool = false
dsa_T_t_1_3604:u32 = dsa_R_ECX_32_1_3602:u32 - 3:u32
dsa_R_CF_1_3605:bool = dsa_R_ECX_32_1_3602:u32 < 3:u32
dsa_R_OF_1_3606:bool =
  high:bool((dsa_R_ECX_32_1_3602:u32 ^ 3:u32) &
            (dsa_R_ECX_32_1_3602:u32 ^ dsa_T_t_1_3604:u32))
dsa_R_AF_1_3607:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_T_t_1_3604:u32 ^ dsa_R_ECX_32_1_3602:u32 ^ 3:u32))
dsa_R_PF_3_3610:bool =
  ~low:bool(let dsa_T_acc_1_3608:u32 :=
                                         dsa_T_t_1_3604:u32 >> 4:u32 ^
                                         dsa_T_t_1_3604:u32 in
            let dsa_T_acc_2_3609:u32 :=
                                         dsa_T_acc_1_3608:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3608:u32 in
            dsa_T_acc_2_3609:u32 >> 1:u32 ^ dsa_T_acc_2_3609:u32)
dsa_R_SF_1_3611:bool = high:bool(dsa_T_t_1_3604:u32)
dsa_R_ZF_1_3612:bool = 0:u32 == dsa_T_t_1_3604:u32
addr 0xdd004310 @asm "mov    bl,BYTE PTR [eax+0x3]" @tid "0"
  @context "R_EBX_32" = 0xdd06d041, -1, u32, wr
  @context "R_EAX_32" = 0xffaf071c, 0, u32, rd
  @context "mem32[0xffaf071f]" = 0x41, -1, u8, rd
label pc_0xdd004310
dsa_R_EAX_32_1_3613:u32 = 0xffaf071c:u32
dsa_R_EBX_32_1_3614:u32 =
  concat:[extract:31:8:[dsa_R_EBX_32_1_3580:u32]][
   pad:u8(dsa_mem_ffaf071f_1_2424:u8)]
addr 0xdd004313 @asm "cmp    bl,BYTE PTR [edx+0x3]" @tid "0"
  @context "R_EBX_32" = 0xdd06d041, -1, u32, rd
  @context "R_EDX_32" = 0x8048cde, 0, u32, rd
  @context "R_EFLAGS" = 0x202, 0, u32, wr
  @context "mem32[0x8048ce1]" = 0x41, 0, u8, rd
label pc_0xdd004313
dsa_mem_8048ce1_1_3615:u8 = low:u8(0x41:u8)
dsa_R_ZF_1_3616:bool = false
dsa_R_AF_1_3617:bool = false
dsa_R_OF_1_3618:bool = false
dsa_R_SF_1_3619:bool = false
dsa_R_DF_1_3620:bool = false
dsa_R_EDX_32_1_3621:u32 = 0x8048cde:u32
dsa_R_CF_1_3622:bool = false
dsa_R_EFLAGS_1_3623:u32 = 0x202:u32
dsa_R_PF_1_3624:bool = false
dsa_T_t_1_3625:u8 =
  low:u8(dsa_R_EBX_32_1_3614:u32) - pad:u8(dsa_mem_8048ce1_1_3615:u8)
dsa_R_CF_1_3626:bool =
  low:u8(dsa_R_EBX_32_1_3614:u32) < pad:u8(dsa_mem_8048ce1_1_3615:u8)
dsa_R_OF_1_3627:bool =
  high:bool((low:u8(dsa_R_EBX_32_1_3614:u32) ^
            pad:u8(dsa_mem_8048ce1_1_3615:u8)) &
            (low:u8(dsa_R_EBX_32_1_3614:u32) ^ dsa_T_t_1_3625:u8))
dsa_R_AF_1_3628:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_3625:u8 ^ low:u8(dsa_R_EBX_32_1_3614:u32) ^
  pad:u8(dsa_mem_8048ce1_1_3615:u8)))
dsa_R_PF_3_3631:bool =
  ~low:bool(let dsa_T_acc_1_3629:u8 :=
                                        dsa_T_t_1_3625:u8 >> 4:u8 ^
                                        dsa_T_t_1_3625:u8 in
            let dsa_T_acc_2_3630:u8 :=
                                        dsa_T_acc_1_3629:u8 >> 2:u8 ^
                                        dsa_T_acc_1_3629:u8 in
            dsa_T_acc_2_3630:u8 >> 1:u8 ^ dsa_T_acc_2_3630:u8)
dsa_R_SF_1_3632:bool = high:bool(dsa_T_t_1_3625:u8)
dsa_R_ZF_1_3633:bool = 0:u8 == dsa_T_t_1_3625:u8
addr 0xdd004316 @asm "jne    0x00000000dd00433f" @tid "0"
  @context "R_EIP" = 0xdd004316, 0, u32, rw
  @context "R_EFLAGS" = 0x246, -1, u32, rd
label pc_0xdd004316
dsa_R_DF_1_3634:bool = false
dsa_R_EIP_1_3635:u32 = 0xdd004316:u32
assert ~~dsa_R_ZF_1_3633:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdd00433f:u32, "nocjmp110"*/
label nocjmp110
addr 0xdd004318 @asm "cmp    ecx,0x4" @tid "0"
  @context "R_ECX_32" = 0x4, 0, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
label pc_0xdd004318
dsa_R_ECX_32_1_3636:u32 = 4:u32
dsa_R_DF_1_3637:bool = false
dsa_T_t_1_3638:u32 = dsa_R_ECX_32_1_3636:u32 - 4:u32
dsa_R_CF_1_3639:bool = dsa_R_ECX_32_1_3636:u32 < 4:u32
dsa_R_OF_1_3640:bool =
  high:bool((dsa_R_ECX_32_1_3636:u32 ^ 4:u32) &
            (dsa_R_ECX_32_1_3636:u32 ^ dsa_T_t_1_3638:u32))
dsa_R_AF_1_3641:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_T_t_1_3638:u32 ^ dsa_R_ECX_32_1_3636:u32 ^ 4:u32))
dsa_R_PF_3_3644:bool =
  ~low:bool(let dsa_T_acc_1_3642:u32 :=
                                         dsa_T_t_1_3638:u32 >> 4:u32 ^
                                         dsa_T_t_1_3638:u32 in
            let dsa_T_acc_2_3643:u32 :=
                                         dsa_T_acc_1_3642:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3642:u32 in
            dsa_T_acc_2_3643:u32 >> 1:u32 ^ dsa_T_acc_2_3643:u32)
dsa_R_SF_1_3645:bool = high:bool(dsa_T_t_1_3638:u32)
dsa_R_ZF_1_3646:bool = 0:u32 == dsa_T_t_1_3638:u32
addr 0xdd004350 @asm "pop    ebx" @tid "0"
  @context "R_EBX_32" = 0xdd06d041, -1, u32, wr
  @context "R_ESP_32" = 0xffaf06b8, 0, u32, rd
  @context "mem32[0xffaf06b8]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf06b9]" = 0xd0, 0, u8, rd
  @context "mem32[0xffaf06ba]" = 0x6, 0, u8, rd
  @context "mem32[0xffaf06bb]" = 0xdd, 0, u8, rd
label pc_0xdd004350
dsa_mem_ffaf06b9_1_3647:u8 = low:u8(0xd0:u8)
dsa_mem_ffaf06ba_1_3648:u8 = low:u8(6:u8)
dsa_mem_ffaf06bb_1_3649:u8 = low:u8(0xdd:u8)
dsa_mem_ffaf06b8_1_3650:u8 = low:u8(0:u8)
dsa_R_ESP_32_1_3651:u32 = 0xffaf06b8:u32
dsa_R_EBX_32_1_3652:u32 =
  pad:u32(dsa_mem_ffaf06bb_1_3649:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf06ba_1_3648:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf06b9_1_3647:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf06b8_1_3650:u8)))
dsa_R_ESP_32_1_3653:u32 = dsa_R_ESP_32_1_3651:u32 + 4:u32
addr 0x80488a0 @asm "mov    edx,DWORD PTR [eax+0x8]" @tid "0"
  @context "R_EDX_32" = 0x8048cde, 0, u32, wr
  @context "R_EAX_32" = 0xffaf071c, 0, u32, rd
  @context "mem32[0xffaf0724]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0725]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0726]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0727]" = 0x41, -1, u8, rd
label pc_0x80488a0
dsa_R_EDX_32_1_3654:u32 = 0x8048cde:u32
dsa_R_EAX_32_1_3655:u32 = 0xffaf071c:u32
dsa_R_EDX_32_1_3656:u32 =
  pad:u32(dsa_mem_ffaf0727_1_2466:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf0726_1_2465:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf0725_1_2447:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf0724_1_2446:u8)))
addr 0x80488a6 @asm "mov    eax,DWORD PTR [eax+0x4]" @tid "0"
  @context "R_EAX_32" = 0xffaf071c, 0, u32, wr
  @context "R_EAX_32" = 0xffaf071c, 0, u32, rd
  @context "mem32[0xffaf0720]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0721]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0722]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0723]" = 0x41, -1, u8, rd
label pc_0x80488a6
dsa_R_EAX_32_1_3657:u32 = 0xffaf071c:u32
dsa_R_EAX_32_1_3658:u32 =
  pad:u32(dsa_mem_ffaf0723_1_2445:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf0722_1_2444:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf0721_1_2426:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf0720_1_2425:u8)))
addr 0x80488a9 @asm "mov    DWORD PTR [esp+0x8],edx" @tid "0"
  @context "R_ESP_32" = 0xffaf06c0, 0, u32, rd
  @context "R_EDX_32" = 0x41414141, -1, u32, rd
  @context "mem32[0xffaf06c8]" = 0x4, 0, u8, wr
  @context "mem32[0xffaf06c9]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf06ca]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf06cb]" = 0x0, 0, u8, wr
label pc_0x80488a9
dsa_mem_ffaf06c9_1_3659:u8 = low:u8(0:u8)
dsa_mem_ffaf06c8_1_3660:u8 = low:u8(4:u8)
dsa_mem_ffaf06ca_1_3661:u8 = low:u8(0:u8)
dsa_mem_ffaf06cb_1_3662:u8 = low:u8(0:u8)
dsa_R_ESP_32_1_3663:u32 = 0xffaf06c0:u32
dsa_mem_ffaf06c8_1_3664:u8 = low:u8(dsa_R_EDX_32_1_3656:u32)
dsa_mem_ffaf06c9_1_3665:u8 = low:u8(dsa_R_EDX_32_1_3656:u32 >> 8:u32)
dsa_mem_ffaf06ca_1_3666:u8 = low:u8(dsa_R_EDX_32_1_3656:u32 >> 0x10:u32)
dsa_mem_ffaf06cb_1_3667:u8 = low:u8(dsa_R_EDX_32_1_3656:u32 >> 0x18:u32)
addr 0x80488ad @asm "mov    DWORD PTR [esp+0x4],eax" @tid "0"
  @context "R_ESP_32" = 0xffaf06c0, 0, u32, rd
  @context "R_EAX_32" = 0x41414141, -1, u32, rd
  @context "mem32[0xffaf06c4]" = 0xde, 0, u8, wr
  @context "mem32[0xffaf06c5]" = 0x8c, 0, u8, wr
  @context "mem32[0xffaf06c6]" = 0x4, 0, u8, wr
  @context "mem32[0xffaf06c7]" = 0x8, 0, u8, wr
label pc_0x80488ad
dsa_mem_ffaf06c6_1_3668:u8 = low:u8(4:u8)
dsa_mem_ffaf06c7_1_3669:u8 = low:u8(8:u8)
dsa_mem_ffaf06c5_1_3670:u8 = low:u8(0x8c:u8)
dsa_mem_ffaf06c4_1_3671:u8 = low:u8(0xde:u8)
dsa_R_ESP_32_1_3672:u32 = 0xffaf06c0:u32
dsa_mem_ffaf06c4_1_3673:u8 = low:u8(dsa_R_EAX_32_1_3658:u32)
dsa_mem_ffaf06c5_1_3674:u8 = low:u8(dsa_R_EAX_32_1_3658:u32 >> 8:u32)
dsa_mem_ffaf06c6_1_3675:u8 = low:u8(dsa_R_EAX_32_1_3658:u32 >> 0x10:u32)
dsa_mem_ffaf06c7_1_3676:u8 = low:u8(dsa_R_EAX_32_1_3658:u32 >> 0x18:u32)
addr 0xdcf0d41f @asm "lea    eax,[esp+0x24]" @tid "0"
  @context "R_EAX_32" = 0x41414141, -1, u32, wr
  @context "R_ESP_32" = 0xffaf06a0, 0, u32, rd
label pc_0xdcf0d41f
dsa_R_ESP_32_1_3677:u32 = 0xffaf06a0:u32
dsa_R_EAX_32_1_3678:u32 = dsa_R_ESP_32_1_3677:u32 + 0x24:u32
addr 0xdcf03894 @asm "mov    edx,DWORD PTR [esi+0x68]" @tid "0"
  @context "R_EDX_32" = 0x41414141, -1, u32, wr
  @context "R_ESI_32" = 0xdd06dac0, 0, u32, rd
  @context "mem32[0xdd06db28]" = 0xff, 0, u8, rd
  @context "mem32[0xdd06db29]" = 0xff, 0, u8, rd
  @context "mem32[0xdd06db2a]" = 0xff, 0, u8, rd
  @context "mem32[0xdd06db2b]" = 0xff, 0, u8, rd
label pc_0xdcf03894
dsa_mem_dd06db2a_1_3679:u8 = low:u8(-1:u8)
dsa_mem_dd06db2b_1_3680:u8 = low:u8(-1:u8)
dsa_mem_dd06db29_1_3681:u8 = low:u8(-1:u8)
dsa_mem_dd06db28_1_3682:u8 = low:u8(-1:u8)
dsa_R_ESI_32_1_3683:u32 = 0xdd06dac0:u32
dsa_R_EDX_32_1_3684:u32 =
  pad:u32(dsa_mem_dd06db2b_1_3680:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_dd06db2a_1_3679:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_dd06db29_1_3681:u8) << 8:u32 |
  pad:u32(dsa_mem_dd06db28_1_3682:u8)))
addr 0xdcf07865 @asm "mov    eax,DWORD PTR [eax]" @tid "0"
  @context "R_EAX_32" = 0xffaf06c4, 0, u32, wr
  @context "R_EAX_32" = 0xffaf06c4, 0, u32, rd
  @context "mem32[0xffaf06c4]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf06c5]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf06c6]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf06c7]" = 0x41, -1, u8, rd
label pc_0xdcf07865
dsa_R_EAX_32_1_3685:u32 = 0xffaf06c4:u32
dsa_R_EAX_32_1_3686:u32 =
  pad:u32(dsa_mem_ffaf06c7_1_3676:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf06c6_1_3675:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf06c5_1_3674:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf06c4_1_3673:u8)))
addr 0xdcf0781b @asm "mov    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0xdcf040f1, 0, u32, wr
  @context "R_EAX_32" = 0x41414141, -1, u32, rd
label pc_0xdcf0781b
dsa_R_ECX_32_1_3687:u32 = 0xdcf040f1:u32
dsa_R_ECX_32_1_3688:u32 = dsa_R_EAX_32_1_3686:u32
addr 0xdcf0781d @asm "mov    edx,eax" @tid "0"
  @context "R_EDX_32" = 0x44, 0, u32, wr
  @context "R_EAX_32" = 0x41414141, -1, u32, rd
label pc_0xdcf0781d
dsa_R_EDX_32_1_3689:u32 = 0x44:u32
dsa_R_EDX_32_1_3690:u32 = dsa_R_EAX_32_1_3686:u32
addr 0xdcf0781f @asm "shr    ecx,0x1f" @tid "0"
  @context "R_ECX_32" = 0x41414141, -1, u32, rw
  @context "R_EFLAGS" = 0x246, 0, u32, wr
label pc_0xdcf0781f
dsa_R_ZF_1_3691:bool = true
dsa_R_AF_1_3692:bool = false
dsa_R_OF_1_3693:bool = false
dsa_R_SF_1_3694:bool = false
dsa_R_DF_1_3695:bool = false
dsa_R_CF_1_3696:bool = false
dsa_R_EFLAGS_1_3697:u32 = 0x246:u32
dsa_R_PF_1_3698:bool = true
dsa_T_origDEST_1_3699:u32 = dsa_R_ECX_32_1_3688:u32
dsa_T_origCOUNT_1_3700:u32 = 0x1f:u32
dsa_R_ECX_32_1_3701:u32 = dsa_R_ECX_32_1_3688:u32 >> 0x1f:u32
dsa_R_CF_1_3702:bool =
  if dsa_T_origCOUNT_1_3700:u32 == 0:u32 then dsa_R_CF_1_3696:bool else
  high:bool(dsa_T_origDEST_1_3699:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_3700:u32)
dsa_R_OF_1_3703:bool =
  if dsa_T_origCOUNT_1_3700:u32 == 0:u32 then dsa_R_OF_1_3693:bool else
  if dsa_T_origCOUNT_1_3700:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_3699:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_3704:bool =
  if dsa_T_origCOUNT_1_3700:u32 == 0:u32 then dsa_R_SF_1_3694:bool else
  high:bool(dsa_R_ECX_32_1_3701:u32)
dsa_R_ZF_1_3705:bool =
  if dsa_T_origCOUNT_1_3700:u32 == 0:u32 then dsa_R_ZF_1_3691:bool else
  0:u32 == dsa_R_ECX_32_1_3701:u32
dsa_R_PF_3_3708:bool =
  if dsa_T_origCOUNT_1_3700:u32 == 0:u32 then dsa_R_PF_1_3698:bool else
  ~low:bool(let dsa_T_acc_1_3706:u32 :=
                                         dsa_R_ECX_32_1_3701:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_3701:u32 in
            let dsa_T_acc_2_3707:u32 :=
                                         dsa_T_acc_1_3706:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3706:u32 in
            dsa_T_acc_2_3707:u32 >> 1:u32 ^ dsa_T_acc_2_3707:u32)
dsa_R_AF_1_3709:bool =
  if dsa_T_origCOUNT_1_3700:u32 == 0:u32 then dsa_R_AF_1_3692:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf07822 @asm "neg    edx" @tid "0"
  @context "R_EDX_32" = 0x41414141, -1, u32, rw
  @context "R_EFLAGS" = 0x247, -1, u32, wr
label pc_0xdcf07822
dsa_R_DF_1_3710:bool = false
dsa_T_t_1_3711:u32 = dsa_R_EDX_32_1_3690:u32
dsa_R_EDX_32_1_3712:u32 = 0:u32 - dsa_R_EDX_32_1_3690:u32
dsa_R_CF_1_3713:bool = if dsa_T_t_1_3711:u32 == 0:u32 then false else true
dsa_R_OF_1_3714:bool =
  if dsa_T_t_1_3711:u32 == 0x80000000:u32 then true else false
dsa_R_AF_1_3715:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_EDX_32_1_3712:u32 ^ dsa_T_t_1_3711:u32 ^ 0:u32))
dsa_R_PF_3_3718:bool =
  ~low:bool(let dsa_T_acc_1_3716:u32 :=
                                         dsa_R_EDX_32_1_3712:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_3712:u32 in
            let dsa_T_acc_2_3717:u32 :=
                                         dsa_T_acc_1_3716:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3716:u32 in
            dsa_T_acc_2_3717:u32 >> 1:u32 ^ dsa_T_acc_2_3717:u32)
dsa_R_SF_1_3719:bool = high:bool(dsa_R_EDX_32_1_3712:u32)
dsa_R_ZF_1_3720:bool = 0:u32 == dsa_R_EDX_32_1_3712:u32
addr 0xdcf07824 @asm "test   ecx,ecx" @tid "0"
  @context "R_ECX_32" = 0x0, -1, u32, rd
  @context "R_ECX_32" = 0x0, -1, u32, rd
  @context "R_EFLAGS" = 0x293, -1, u32, wr
label pc_0xdcf07824
dsa_R_DF_1_3721:bool = false
dsa_T_t_1_3722:u32 = dsa_R_ECX_32_1_3701:u32 & dsa_R_ECX_32_1_3701:u32
dsa_R_OF_1_3723:bool = false
dsa_R_CF_1_3724:bool = false
dsa_R_AF_1_3725:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_3728:bool =
  ~low:bool(let dsa_T_acc_1_3726:u32 :=
                                         dsa_T_t_1_3722:u32 >> 4:u32 ^
                                         dsa_T_t_1_3722:u32 in
            let dsa_T_acc_2_3727:u32 :=
                                         dsa_T_acc_1_3726:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3726:u32 in
            dsa_T_acc_2_3727:u32 >> 1:u32 ^ dsa_T_acc_2_3727:u32)
dsa_R_SF_1_3729:bool = high:bool(dsa_T_t_1_3722:u32)
dsa_R_ZF_1_3730:bool = 0:u32 == dsa_T_t_1_3722:u32
addr 0xdcf07826 @asm "cmovne eax,edx" @tid "0"
  @context "R_EAX_32" = 0x41414141, -1, u32, wr
  @context "R_EDX_32" = 0xbebebebf, -1, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, rd
label pc_0xdcf07826
dsa_R_DF_1_3731:bool = false
dsa_R_EAX_32_1_3732:u32 =
  if ~dsa_R_ZF_1_3730:bool then dsa_R_EDX_32_1_3712:u32 else
  dsa_R_EAX_32_1_3686:u32
addr 0xdcf07829 @asm "mov    DWORD PTR [ebp-0x4bc],ecx" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_ECX_32" = 0x0, -1, u32, rd
  @context "mem32[0xffaf01dc]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf01dd]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf01de]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf01df]" = 0x0, 0, u8, wr
label pc_0xdcf07829
dsa_mem_ffaf01dc_1_3733:u8 = low:u8(0:u8)
dsa_mem_ffaf01de_1_3734:u8 = low:u8(0:u8)
dsa_mem_ffaf01dd_1_3735:u8 = low:u8(0:u8)
dsa_mem_ffaf01df_1_3736:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_3737:u32 = 0xffaf0698:u32
dsa_mem_ffaf01dc_1_3738:u8 = low:u8(dsa_R_ECX_32_1_3701:u32)
dsa_mem_ffaf01dd_1_3739:u8 = low:u8(dsa_R_ECX_32_1_3701:u32 >> 8:u32)
dsa_mem_ffaf01de_1_3740:u8 = low:u8(dsa_R_ECX_32_1_3701:u32 >> 0x10:u32)
dsa_mem_ffaf01df_1_3741:u8 = low:u8(dsa_R_ECX_32_1_3701:u32 >> 0x18:u32)
addr 0xdcf0782f @asm "mov    DWORD PTR [ebp-0x4b8],eax" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EAX_32" = 0x41414141, -1, u32, rd
  @context "mem32[0xffaf01e0]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf01e1]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf01e2]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf01e3]" = 0x0, 0, u8, wr
label pc_0xdcf0782f
dsa_mem_ffaf01e1_1_3742:u8 = low:u8(0:u8)
dsa_mem_ffaf01e0_1_3743:u8 = low:u8(0:u8)
dsa_mem_ffaf01e3_1_3744:u8 = low:u8(0:u8)
dsa_mem_ffaf01e2_1_3745:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_3746:u32 = 0xffaf0698:u32
dsa_mem_ffaf01e0_1_3747:u8 = low:u8(dsa_R_EAX_32_1_3732:u32)
dsa_mem_ffaf01e1_1_3748:u8 = low:u8(dsa_R_EAX_32_1_3732:u32 >> 8:u32)
dsa_mem_ffaf01e2_1_3749:u8 = low:u8(dsa_R_EAX_32_1_3732:u32 >> 0x10:u32)
dsa_mem_ffaf01e3_1_3750:u8 = low:u8(dsa_R_EAX_32_1_3732:u32 >> 0x18:u32)
addr 0xdcf04456 @asm "cmp    DWORD PTR [ebp-0x49c],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
  @context "mem32[0xffaf01fc]" = 0xff, 0, u8, rd
  @context "mem32[0xffaf01fd]" = 0xff, 0, u8, rd
  @context "mem32[0xffaf01fe]" = 0xff, 0, u8, rd
  @context "mem32[0xffaf01ff]" = 0xff, 0, u8, rd
label pc_0xdcf04456
dsa_mem_ffaf01fe_1_3751:u8 = low:u8(-1:u8)
dsa_mem_ffaf01fc_1_3752:u8 = low:u8(-1:u8)
dsa_mem_ffaf01fd_1_3753:u8 = low:u8(-1:u8)
dsa_mem_ffaf01ff_1_3754:u8 = low:u8(-1:u8)
dsa_R_EBP_32_1_3755:u32 = 0xffaf0698:u32
dsa_R_DF_1_3756:bool = false
dsa_T_t_1_3757:u32 =
  (pad:u32(dsa_mem_ffaf01ff_1_3754:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01fe_1_3751:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01fd_1_3753:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01fc_1_3752:u8)))) - 0:u32
dsa_R_CF_1_3758:bool =
  (pad:u32(dsa_mem_ffaf01ff_1_3754:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01fe_1_3751:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01fd_1_3753:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01fc_1_3752:u8)))) < 0:u32
dsa_R_OF_1_3759:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01ff_1_3754:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01fe_1_3751:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01fd_1_3753:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01fc_1_3752:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01ff_1_3754:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01fe_1_3751:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01fd_1_3753:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01fc_1_3752:u8)))) ^ dsa_T_t_1_3757:u32))
dsa_R_AF_1_3760:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_3757:u32 ^
   (pad:u32(dsa_mem_ffaf01ff_1_3754:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01fe_1_3751:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01fd_1_3753:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01fc_1_3752:u8)))) ^ 0:u32))
dsa_R_PF_3_3763:bool =
  ~low:bool(let dsa_T_acc_1_3761:u32 :=
                                         dsa_T_t_1_3757:u32 >> 4:u32 ^
                                         dsa_T_t_1_3757:u32 in
            let dsa_T_acc_2_3762:u32 :=
                                         dsa_T_acc_1_3761:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3761:u32 in
            dsa_T_acc_2_3762:u32 >> 1:u32 ^ dsa_T_acc_2_3762:u32)
dsa_R_SF_1_3764:bool = high:bool(dsa_T_t_1_3757:u32)
dsa_R_ZF_1_3765:bool = 0:u32 == dsa_T_t_1_3757:u32
addr 0xdcf068fd @asm "xor    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x41414141, -1, u32, wr
  @context "R_EAX_32" = 0x41414141, -1, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
label pc_0xdcf068fd
dsa_R_ZF_1_3766:bool = false
dsa_R_AF_1_3767:bool = false
dsa_R_OF_1_3768:bool = false
dsa_R_SF_1_3769:bool = true
dsa_R_DF_1_3770:bool = false
dsa_R_CF_1_3771:bool = false
dsa_R_EFLAGS_1_3772:u32 = 0x286:u32
dsa_R_PF_1_3773:bool = true
dsa_R_EAX_32_1_3774:u32 = 0:u32
dsa_R_AF_1_3775:bool = unknown "AF is undefined after xor":bool
dsa_R_ZF_1_3776:bool = true
dsa_R_PF_1_3777:bool = true
dsa_R_OF_1_3778:bool = false
dsa_R_CF_1_3779:bool = false
dsa_R_SF_1_3780:bool = false
addr 0xdcf0691b @asm "mov    eax,DWORD PTR [ebp-0x4b8]" @tid "0"
  @context "R_EAX_32" = 0xa, 0, u32, wr
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "mem32[0xffaf01e0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e3]" = 0x41, -1, u8, rd
label pc_0xdcf0691b
dsa_R_EBP_32_1_3781:u32 = 0xffaf0698:u32
dsa_R_EAX_32_1_3782:u32 = 0xa:u32
dsa_R_EAX_32_1_3783:u32 =
  pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))
addr 0xdcf06921 @asm "mov    DWORD PTR [esp],eax" @tid "0"
  @context "R_ESP_32" = 0xffaf0180, 0, u32, rd
  @context "R_EAX_32" = 0x41414141, -1, u32, rd
  @context "mem32[0xffaf0180]" = 0xc0, 0, u8, wr
  @context "mem32[0xffaf0181]" = 0xda, 0, u8, wr
  @context "mem32[0xffaf0182]" = 0x6, 0, u8, wr
  @context "mem32[0xffaf0183]" = 0xdd, 0, u8, wr
label pc_0xdcf06921
dsa_mem_ffaf0181_1_3784:u8 = low:u8(0xda:u8)
dsa_mem_ffaf0183_1_3785:u8 = low:u8(0xdd:u8)
dsa_mem_ffaf0180_1_3786:u8 = low:u8(0xc0:u8)
dsa_mem_ffaf0182_1_3787:u8 = low:u8(6:u8)
dsa_R_ESP_32_1_3788:u32 = 0xffaf0180:u32
dsa_mem_ffaf0180_1_3789:u8 = low:u8(dsa_R_EAX_32_1_3783:u32)
dsa_mem_ffaf0181_1_3790:u8 = low:u8(dsa_R_EAX_32_1_3783:u32 >> 8:u32)
dsa_mem_ffaf0182_1_3791:u8 = low:u8(dsa_R_EAX_32_1_3783:u32 >> 0x10:u32)
dsa_mem_ffaf0183_1_3792:u8 = low:u8(dsa_R_EAX_32_1_3783:u32 >> 0x18:u32)
addr 0xdcf03174 @asm "mov    eax,DWORD PTR [esp+0x20]" @tid "0"
  @context "R_EAX_32" = 0x41414141, -1, u32, wr
  @context "R_ESP_32" = 0xffaf016c, 0, u32, rd
  @context "mem32[0xffaf018c]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf018d]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf018e]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf018f]" = 0x0, 0, u8, rd
label pc_0xdcf03174
dsa_mem_ffaf018d_1_3793:u8 = low:u8(0:u8)
dsa_mem_ffaf018e_1_3794:u8 = low:u8(0:u8)
dsa_mem_ffaf018f_1_3795:u8 = low:u8(0:u8)
dsa_mem_ffaf018c_1_3796:u8 = low:u8(0:u8)
dsa_R_ESP_32_1_3797:u32 = 0xffaf016c:u32
dsa_R_EAX_32_1_3798:u32 =
  pad:u32(dsa_mem_ffaf018f_1_3795:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf018e_1_3794:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf018d_1_3793:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf018c_1_3796:u8)))
addr 0xdcf03187 @asm "mov    ecx,DWORD PTR [esp+0x14]" @tid "0"
  @context "R_ECX_32" = 0x0, -1, u32, wr
  @context "R_ESP_32" = 0xffaf016c, 0, u32, rd
  @context "mem32[0xffaf0180]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0181]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0182]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0183]" = 0x41, -1, u8, rd
label pc_0xdcf03187
dsa_R_ESP_32_1_3799:u32 = 0xffaf016c:u32
dsa_R_ECX_32_1_3800:u32 =
  pad:u32(dsa_mem_ffaf0183_1_3792:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf0182_1_3791:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf0181_1_3790:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf0180_1_3789:u8)))
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0xdd01cca0, 0, u32, wr
  @context "R_ECX_32" = 0x41414141, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_3801:u32 = 0xdd01cca0:u32
dsa_R_EAX_32_1_3802:u32 = dsa_R_ECX_32_1_3800:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x41414141, -1, u32, rw
  @context "R_EDX_32" = 0xbebebebf, -1, u32, wr
  @context "R_EFLAGS" = 0x292, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_3803:bool = false
dsa_R_EBP_32_1_3804:u32 = 0xcccccccd:u32
dsa_R_AF_1_3805:bool = true
dsa_R_OF_1_3806:bool = false
dsa_R_SF_1_3807:bool = true
dsa_R_DF_1_3808:bool = false
dsa_R_CF_1_3809:bool = false
dsa_R_EFLAGS_1_3810:u32 = 0x292:u32
dsa_R_PF_1_3811:bool = false
dsa_T_t_1_3812:u64 =
  pad:u64(dsa_R_EAX_32_1_3802:u32) * pad:u64(dsa_R_EBP_32_1_3804:u32)
dsa_R_EAX_32_1_3813:u32 = extract:31:0:[dsa_T_t_1_3812:u64]
dsa_R_EDX_32_1_3814:u32 = extract:63:32:[dsa_T_t_1_3812:u64]
dsa_R_OF_1_3815:bool = extract:63:32:[dsa_T_t_1_3812:u64] <> 0:u32
dsa_R_CF_1_3816:bool = extract:63:32:[dsa_T_t_1_3812:u64] <> 0:u32
dsa_R_SF_1_3817:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_3818:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_3819:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_3820:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x34343434, -1, u32, rw
  @context "R_EFLAGS" = 0xa03, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_3821:bool = false
dsa_T_origDEST_1_3822:u32 = dsa_R_EDX_32_1_3814:u32
dsa_T_origCOUNT_1_3823:u32 = 3:u32
dsa_R_EDX_32_1_3824:u32 = dsa_R_EDX_32_1_3814:u32 >> 3:u32
dsa_R_CF_1_3825:bool =
  if dsa_T_origCOUNT_1_3823:u32 == 0:u32 then dsa_R_CF_1_3816:bool else
  high:bool(dsa_T_origDEST_1_3822:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_3823:u32)
dsa_R_OF_1_3826:bool =
  if dsa_T_origCOUNT_1_3823:u32 == 0:u32 then dsa_R_OF_1_3815:bool else
  if dsa_T_origCOUNT_1_3823:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_3822:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_3827:bool =
  if dsa_T_origCOUNT_1_3823:u32 == 0:u32 then dsa_R_SF_1_3817:bool else
  high:bool(dsa_R_EDX_32_1_3824:u32)
dsa_R_ZF_1_3828:bool =
  if dsa_T_origCOUNT_1_3823:u32 == 0:u32 then dsa_R_ZF_1_3818:bool else
  0:u32 == dsa_R_EDX_32_1_3824:u32
dsa_R_PF_3_3831:bool =
  if dsa_T_origCOUNT_1_3823:u32 == 0:u32 then dsa_R_PF_1_3820:bool else
  ~low:bool(let dsa_T_acc_1_3829:u32 :=
                                         dsa_R_EDX_32_1_3824:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_3824:u32 in
            let dsa_T_acc_2_3830:u32 :=
                                         dsa_T_acc_1_3829:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3829:u32 in
            dsa_T_acc_2_3830:u32 >> 1:u32 ^ dsa_T_acc_2_3830:u32)
dsa_R_AF_1_3832:bool =
  if dsa_T_origCOUNT_1_3823:u32 == 0:u32 then dsa_R_AF_1_3819:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0xd0d0d0d, -1, u32, wr
  @context "R_EDX_32" = 0x6868686, -1, u32, rd
  @context "R_EDX_32" = 0x6868686, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_3833:u32 =
  dsa_R_EDX_32_1_3824:u32 + (dsa_R_EDX_32_1_3824:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x20a0a09e, -1, u32, rw
  @context "R_EAX_32" = 0x20a0a09e, -1, u32, rd
  @context "R_EFLAGS" = 0x203, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_3834:bool = false
dsa_T_t1_1_3835:u32 = dsa_R_EAX_32_1_3833:u32
dsa_T_t2_1_3836:u32 = dsa_R_EAX_32_1_3833:u32
dsa_R_EAX_32_1_3837:u32 = dsa_R_EAX_32_1_3833:u32 + dsa_T_t2_1_3836:u32
dsa_R_CF_1_3838:bool = dsa_R_EAX_32_1_3837:u32 < dsa_T_t1_1_3835:u32
dsa_R_OF_1_3839:bool =
  high:bool((dsa_T_t1_1_3835:u32 ^ ~dsa_T_t2_1_3836:u32) &
            (dsa_T_t1_1_3835:u32 ^ dsa_R_EAX_32_1_3837:u32))
dsa_R_AF_1_3840:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_3837:u32 ^ dsa_T_t1_1_3835:u32 ^ dsa_T_t2_1_3836:u32))
dsa_R_PF_3_3843:bool =
  ~low:bool(let dsa_T_acc_1_3841:u32 :=
                                         dsa_R_EAX_32_1_3837:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_3837:u32 in
            let dsa_T_acc_2_3842:u32 :=
                                         dsa_T_acc_1_3841:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3841:u32 in
            dsa_T_acc_2_3842:u32 >> 1:u32 ^ dsa_T_acc_2_3842:u32)
dsa_R_SF_1_3844:bool = high:bool(dsa_R_EAX_32_1_3837:u32)
dsa_R_ZF_1_3845:bool = 0:u32 == dsa_R_EAX_32_1_3837:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x41414141, -1, u32, rw
  @context "R_EAX_32" = 0x4141413c, -1, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_3846:bool = false
dsa_T_t_1_3847:u32 = dsa_R_ECX_32_1_3800:u32
dsa_R_ECX_32_1_3848:u32 = dsa_R_ECX_32_1_3800:u32 - dsa_R_EAX_32_1_3837:u32
dsa_R_CF_1_3849:bool = dsa_T_t_1_3847:u32 < dsa_R_EAX_32_1_3837:u32
dsa_R_OF_1_3850:bool =
  high:bool((dsa_T_t_1_3847:u32 ^ dsa_R_EAX_32_1_3837:u32) &
            (dsa_T_t_1_3847:u32 ^ dsa_R_ECX_32_1_3848:u32))
dsa_R_AF_1_3851:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_3848:u32 ^ dsa_T_t_1_3847:u32 ^ dsa_R_EAX_32_1_3837:u32))
dsa_R_PF_3_3854:bool =
  ~low:bool(let dsa_T_acc_1_3852:u32 :=
                                         dsa_R_ECX_32_1_3848:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_3848:u32 in
            let dsa_T_acc_2_3853:u32 :=
                                         dsa_T_acc_1_3852:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3852:u32 in
            dsa_T_acc_2_3853:u32 >> 1:u32 ^ dsa_T_acc_2_3853:u32)
dsa_R_SF_1_3855:bool = high:bool(dsa_R_ECX_32_1_3848:u32)
dsa_R_ZF_1_3856:bool = 0:u32 == dsa_R_ECX_32_1_3848:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x6868686, -1, u32, rd
  @context "R_EDX_32" = 0x6868686, -1, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_3857:bool = false
dsa_T_t_1_3858:u32 = dsa_R_EDX_32_1_3824:u32 & dsa_R_EDX_32_1_3824:u32
dsa_R_OF_1_3859:bool = false
dsa_R_CF_1_3860:bool = false
dsa_R_AF_1_3861:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_3864:bool =
  ~low:bool(let dsa_T_acc_1_3862:u32 :=
                                         dsa_T_t_1_3858:u32 >> 4:u32 ^
                                         dsa_T_t_1_3858:u32 in
            let dsa_T_acc_2_3863:u32 :=
                                         dsa_T_acc_1_3862:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3862:u32 in
            dsa_T_acc_2_3863:u32 >> 1:u32 ^ dsa_T_acc_2_3863:u32)
dsa_R_SF_1_3865:bool = high:bool(dsa_T_t_1_3858:u32)
dsa_R_ZF_1_3866:bool = 0:u32 == dsa_T_t_1_3858:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x4141413c, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x5, -1, u32, rd
  @context "mem32[0xdd01cc65]" = 0x35, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc65_1_3867:u8 = low:u8(0x35:u8)
dsa_R_EDI_32_1_3868:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_3869:u32 = pad:u32(pad:u8(dsa_mem_dd01cc65_1_3867:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x5, -1, u32, wr
  @context "R_EDX_32" = 0x6868686, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_3870:u32 = dsa_R_EDX_32_1_3824:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf067f, 0, u32, rd
  @context "R_EAX_32" = 0x35, -1, u32, rd
  @context "mem32[0xffaf067f]" = 0xdc, 0, u8, wr
label pc_0xdcf03221
dsa_mem_ffaf067f_1_3871:u8 = low:u8(0xdc:u8)
dsa_R_ESI_32_1_3872:u32 = 0xffaf067f:u32
dsa_mem_ffaf067f_1_3873:u8 = low:u8(low:u8(dsa_R_EAX_32_1_3869:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_3874:bool = false
dsa_R_EIP_1_3875:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_3866:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp111"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x35, -1, u32, wr
  @context "R_ECX_32" = 0x6868686, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_3876:u32 = dsa_R_ECX_32_1_3870:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf067f, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_3877:u32 = 0xffaf067f:u32
dsa_R_DF_1_3878:bool = false
dsa_T_t_1_3879:u32 = dsa_R_ESI_32_1_3877:u32
dsa_R_ESI_32_1_3880:u32 = dsa_R_ESI_32_1_3877:u32 - 1:u32
dsa_R_CF_1_3881:bool = dsa_T_t_1_3879:u32 < 1:u32
dsa_R_OF_1_3882:bool =
  high:bool((dsa_T_t_1_3879:u32 ^ 1:u32) &
            (dsa_T_t_1_3879:u32 ^ dsa_R_ESI_32_1_3880:u32))
dsa_R_AF_1_3883:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_3880:u32 ^ dsa_T_t_1_3879:u32 ^ 1:u32))
dsa_R_PF_3_3886:bool =
  ~low:bool(let dsa_T_acc_1_3884:u32 :=
                                         dsa_R_ESI_32_1_3880:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_3880:u32 in
            let dsa_T_acc_2_3885:u32 :=
                                         dsa_T_acc_1_3884:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3884:u32 in
            dsa_T_acc_2_3885:u32 >> 1:u32 ^ dsa_T_acc_2_3885:u32)
dsa_R_SF_1_3887:bool = high:bool(dsa_R_ESI_32_1_3880:u32)
dsa_R_ZF_1_3888:bool = 0:u32 == dsa_R_ESI_32_1_3880:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x6868686, -1, u32, rw
  @context "R_EDX_32" = 0x6868686, -1, u32, wr
  @context "R_EFLAGS" = 0x286, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_3889:bool = false
dsa_R_EBP_32_1_3890:u32 = 0xcccccccd:u32
dsa_R_AF_1_3891:bool = false
dsa_R_OF_1_3892:bool = false
dsa_R_SF_1_3893:bool = true
dsa_R_DF_1_3894:bool = false
dsa_R_CF_1_3895:bool = false
dsa_R_EFLAGS_1_3896:u32 = 0x286:u32
dsa_R_PF_1_3897:bool = true
dsa_T_t_1_3898:u64 =
  pad:u64(dsa_R_EAX_32_1_3876:u32) * pad:u64(dsa_R_EBP_32_1_3890:u32)
dsa_R_EAX_32_1_3899:u32 = extract:31:0:[dsa_T_t_1_3898:u64]
dsa_R_EDX_32_1_3900:u32 = extract:63:32:[dsa_T_t_1_3898:u64]
dsa_R_OF_1_3901:bool = extract:63:32:[dsa_T_t_1_3898:u64] <> 0:u32
dsa_R_CF_1_3902:bool = extract:63:32:[dsa_T_t_1_3898:u64] <> 0:u32
dsa_R_SF_1_3903:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_3904:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_3905:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_3906:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x5386b9e, -1, u32, rw
  @context "R_EFLAGS" = 0xa07, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_3907:bool = false
dsa_T_origDEST_1_3908:u32 = dsa_R_EDX_32_1_3900:u32
dsa_T_origCOUNT_1_3909:u32 = 3:u32
dsa_R_EDX_32_1_3910:u32 = dsa_R_EDX_32_1_3900:u32 >> 3:u32
dsa_R_CF_1_3911:bool =
  if dsa_T_origCOUNT_1_3909:u32 == 0:u32 then dsa_R_CF_1_3902:bool else
  high:bool(dsa_T_origDEST_1_3908:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_3909:u32)
dsa_R_OF_1_3912:bool =
  if dsa_T_origCOUNT_1_3909:u32 == 0:u32 then dsa_R_OF_1_3901:bool else
  if dsa_T_origCOUNT_1_3909:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_3908:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_3913:bool =
  if dsa_T_origCOUNT_1_3909:u32 == 0:u32 then dsa_R_SF_1_3903:bool else
  high:bool(dsa_R_EDX_32_1_3910:u32)
dsa_R_ZF_1_3914:bool =
  if dsa_T_origCOUNT_1_3909:u32 == 0:u32 then dsa_R_ZF_1_3904:bool else
  0:u32 == dsa_R_EDX_32_1_3910:u32
dsa_R_PF_3_3917:bool =
  if dsa_T_origCOUNT_1_3909:u32 == 0:u32 then dsa_R_PF_1_3906:bool else
  ~low:bool(let dsa_T_acc_1_3915:u32 :=
                                         dsa_R_EDX_32_1_3910:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_3910:u32 in
            let dsa_T_acc_2_3916:u32 :=
                                         dsa_T_acc_1_3915:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3915:u32 in
            dsa_T_acc_2_3916:u32 >> 1:u32 ^ dsa_T_acc_2_3916:u32)
dsa_R_AF_1_3918:bool =
  if dsa_T_origCOUNT_1_3909:u32 == 0:u32 then dsa_R_AF_1_3905:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x67b4814e, -1, u32, wr
  @context "R_EDX_32" = 0xa70d73, -1, u32, rd
  @context "R_EDX_32" = 0xa70d73, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_3919:u32 =
  dsa_R_EDX_32_1_3910:u32 + (dsa_R_EDX_32_1_3910:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x343433f, -1, u32, rw
  @context "R_EAX_32" = 0x343433f, -1, u32, rd
  @context "R_EFLAGS" = 0x203, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_3920:bool = false
dsa_T_t1_1_3921:u32 = dsa_R_EAX_32_1_3919:u32
dsa_T_t2_1_3922:u32 = dsa_R_EAX_32_1_3919:u32
dsa_R_EAX_32_1_3923:u32 = dsa_R_EAX_32_1_3919:u32 + dsa_T_t2_1_3922:u32
dsa_R_CF_1_3924:bool = dsa_R_EAX_32_1_3923:u32 < dsa_T_t1_1_3921:u32
dsa_R_OF_1_3925:bool =
  high:bool((dsa_T_t1_1_3921:u32 ^ ~dsa_T_t2_1_3922:u32) &
            (dsa_T_t1_1_3921:u32 ^ dsa_R_EAX_32_1_3923:u32))
dsa_R_AF_1_3926:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_3923:u32 ^ dsa_T_t1_1_3921:u32 ^ dsa_T_t2_1_3922:u32))
dsa_R_PF_3_3929:bool =
  ~low:bool(let dsa_T_acc_1_3927:u32 :=
                                         dsa_R_EAX_32_1_3923:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_3923:u32 in
            let dsa_T_acc_2_3928:u32 :=
                                         dsa_T_acc_1_3927:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3927:u32 in
            dsa_T_acc_2_3928:u32 >> 1:u32 ^ dsa_T_acc_2_3928:u32)
dsa_R_SF_1_3930:bool = high:bool(dsa_R_EAX_32_1_3923:u32)
dsa_R_ZF_1_3931:bool = 0:u32 == dsa_R_EAX_32_1_3923:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x6868686, -1, u32, rw
  @context "R_EAX_32" = 0x686867e, -1, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_3932:bool = false
dsa_T_t_1_3933:u32 = dsa_R_ECX_32_1_3870:u32
dsa_R_ECX_32_1_3934:u32 = dsa_R_ECX_32_1_3870:u32 - dsa_R_EAX_32_1_3923:u32
dsa_R_CF_1_3935:bool = dsa_T_t_1_3933:u32 < dsa_R_EAX_32_1_3923:u32
dsa_R_OF_1_3936:bool =
  high:bool((dsa_T_t_1_3933:u32 ^ dsa_R_EAX_32_1_3923:u32) &
            (dsa_T_t_1_3933:u32 ^ dsa_R_ECX_32_1_3934:u32))
dsa_R_AF_1_3937:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_3934:u32 ^ dsa_T_t_1_3933:u32 ^ dsa_R_EAX_32_1_3923:u32))
dsa_R_PF_3_3940:bool =
  ~low:bool(let dsa_T_acc_1_3938:u32 :=
                                         dsa_R_ECX_32_1_3934:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_3934:u32 in
            let dsa_T_acc_2_3939:u32 :=
                                         dsa_T_acc_1_3938:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3938:u32 in
            dsa_T_acc_2_3939:u32 >> 1:u32 ^ dsa_T_acc_2_3939:u32)
dsa_R_SF_1_3941:bool = high:bool(dsa_R_ECX_32_1_3934:u32)
dsa_R_ZF_1_3942:bool = 0:u32 == dsa_R_ECX_32_1_3934:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0xa70d73, -1, u32, rd
  @context "R_EDX_32" = 0xa70d73, -1, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_3943:bool = false
dsa_T_t_1_3944:u32 = dsa_R_EDX_32_1_3910:u32 & dsa_R_EDX_32_1_3910:u32
dsa_R_OF_1_3945:bool = false
dsa_R_CF_1_3946:bool = false
dsa_R_AF_1_3947:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_3950:bool =
  ~low:bool(let dsa_T_acc_1_3948:u32 :=
                                         dsa_T_t_1_3944:u32 >> 4:u32 ^
                                         dsa_T_t_1_3944:u32 in
            let dsa_T_acc_2_3949:u32 :=
                                         dsa_T_acc_1_3948:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3948:u32 in
            dsa_T_acc_2_3949:u32 >> 1:u32 ^ dsa_T_acc_2_3949:u32)
dsa_R_SF_1_3951:bool = high:bool(dsa_T_t_1_3944:u32)
dsa_R_ZF_1_3952:bool = 0:u32 == dsa_T_t_1_3944:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x686867e, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x8, -1, u32, rd
  @context "mem32[0xdd01cc68]" = 0x38, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc68_1_3953:u8 = low:u8(0x38:u8)
dsa_R_EDI_32_1_3954:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_3955:u32 = pad:u32(pad:u8(dsa_mem_dd01cc68_1_3953:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x8, -1, u32, wr
  @context "R_EDX_32" = 0xa70d73, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_3956:u32 = dsa_R_EDX_32_1_3910:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf067e, 0, u32, rd
  @context "R_EAX_32" = 0x38, -1, u32, rd
  @context "mem32[0xffaf067e]" = 0xf3, 0, u8, wr
label pc_0xdcf03221
dsa_mem_ffaf067e_1_3957:u8 = low:u8(0xf3:u8)
dsa_R_ESI_32_1_3958:u32 = 0xffaf067e:u32
dsa_mem_ffaf067e_1_3959:u8 = low:u8(low:u8(dsa_R_EAX_32_1_3955:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_3960:bool = false
dsa_R_EIP_1_3961:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_3952:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp112"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x38, -1, u32, wr
  @context "R_ECX_32" = 0xa70d73, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_3962:u32 = dsa_R_ECX_32_1_3956:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf067e, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_3963:u32 = 0xffaf067e:u32
dsa_R_DF_1_3964:bool = false
dsa_T_t_1_3965:u32 = dsa_R_ESI_32_1_3963:u32
dsa_R_ESI_32_1_3966:u32 = dsa_R_ESI_32_1_3963:u32 - 1:u32
dsa_R_CF_1_3967:bool = dsa_T_t_1_3965:u32 < 1:u32
dsa_R_OF_1_3968:bool =
  high:bool((dsa_T_t_1_3965:u32 ^ 1:u32) &
            (dsa_T_t_1_3965:u32 ^ dsa_R_ESI_32_1_3966:u32))
dsa_R_AF_1_3969:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_3966:u32 ^ dsa_T_t_1_3965:u32 ^ 1:u32))
dsa_R_PF_3_3972:bool =
  ~low:bool(let dsa_T_acc_1_3970:u32 :=
                                         dsa_R_ESI_32_1_3966:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_3966:u32 in
            let dsa_T_acc_2_3971:u32 :=
                                         dsa_T_acc_1_3970:u32 >> 2:u32 ^
                                         dsa_T_acc_1_3970:u32 in
            dsa_T_acc_2_3971:u32 >> 1:u32 ^ dsa_T_acc_2_3971:u32)
dsa_R_SF_1_3973:bool = high:bool(dsa_R_ESI_32_1_3966:u32)
dsa_R_ZF_1_3974:bool = 0:u32 == dsa_R_ESI_32_1_3966:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0xa70d73, -1, u32, rw
  @context "R_EDX_32" = 0xa70d73, -1, u32, wr
  @context "R_EFLAGS" = 0x286, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_3975:bool = false
dsa_R_EBP_32_1_3976:u32 = 0xcccccccd:u32
dsa_R_AF_1_3977:bool = false
dsa_R_OF_1_3978:bool = false
dsa_R_SF_1_3979:bool = true
dsa_R_DF_1_3980:bool = false
dsa_R_CF_1_3981:bool = false
dsa_R_EFLAGS_1_3982:u32 = 0x286:u32
dsa_R_PF_1_3983:bool = true
dsa_T_t_1_3984:u64 =
  pad:u64(dsa_R_EAX_32_1_3962:u32) * pad:u64(dsa_R_EBP_32_1_3976:u32)
dsa_R_EAX_32_1_3985:u32 = extract:31:0:[dsa_T_t_1_3984:u64]
dsa_R_EDX_32_1_3986:u32 = extract:63:32:[dsa_T_t_1_3984:u64]
dsa_R_OF_1_3987:bool = extract:63:32:[dsa_T_t_1_3984:u64] <> 0:u32
dsa_R_CF_1_3988:bool = extract:63:32:[dsa_T_t_1_3984:u64] <> 0:u32
dsa_R_SF_1_3989:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_3990:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_3991:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_3992:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x85a45c, -1, u32, rw
  @context "R_EFLAGS" = 0xa07, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_3993:bool = false
dsa_T_origDEST_1_3994:u32 = dsa_R_EDX_32_1_3986:u32
dsa_T_origCOUNT_1_3995:u32 = 3:u32
dsa_R_EDX_32_1_3996:u32 = dsa_R_EDX_32_1_3986:u32 >> 3:u32
dsa_R_CF_1_3997:bool =
  if dsa_T_origCOUNT_1_3995:u32 == 0:u32 then dsa_R_CF_1_3988:bool else
  high:bool(dsa_T_origDEST_1_3994:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_3995:u32)
dsa_R_OF_1_3998:bool =
  if dsa_T_origCOUNT_1_3995:u32 == 0:u32 then dsa_R_OF_1_3987:bool else
  if dsa_T_origCOUNT_1_3995:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_3994:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_3999:bool =
  if dsa_T_origCOUNT_1_3995:u32 == 0:u32 then dsa_R_SF_1_3989:bool else
  high:bool(dsa_R_EDX_32_1_3996:u32)
dsa_R_ZF_1_4000:bool =
  if dsa_T_origCOUNT_1_3995:u32 == 0:u32 then dsa_R_ZF_1_3990:bool else
  0:u32 == dsa_R_EDX_32_1_3996:u32
dsa_R_PF_3_4003:bool =
  if dsa_T_origCOUNT_1_3995:u32 == 0:u32 then dsa_R_PF_1_3992:bool else
  ~low:bool(let dsa_T_acc_1_4001:u32 :=
                                         dsa_R_EDX_32_1_3996:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_3996:u32 in
            let dsa_T_acc_2_4002:u32 :=
                                         dsa_T_acc_1_4001:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4001:u32 in
            dsa_T_acc_2_4002:u32 >> 1:u32 ^ dsa_T_acc_2_4002:u32)
dsa_R_AF_1_4004:bool =
  if dsa_T_origCOUNT_1_3995:u32 == 0:u32 then dsa_R_AF_1_3991:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x216917, -1, u32, wr
  @context "R_EDX_32" = 0x10b48b, -1, u32, rd
  @context "R_EDX_32" = 0x10b48b, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_4005:u32 =
  dsa_R_EDX_32_1_3996:u32 + (dsa_R_EDX_32_1_3996:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x5386b7, -1, u32, rw
  @context "R_EAX_32" = 0x5386b7, -1, u32, rd
  @context "R_EFLAGS" = 0x207, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_4006:bool = false
dsa_T_t1_1_4007:u32 = dsa_R_EAX_32_1_4005:u32
dsa_T_t2_1_4008:u32 = dsa_R_EAX_32_1_4005:u32
dsa_R_EAX_32_1_4009:u32 = dsa_R_EAX_32_1_4005:u32 + dsa_T_t2_1_4008:u32
dsa_R_CF_1_4010:bool = dsa_R_EAX_32_1_4009:u32 < dsa_T_t1_1_4007:u32
dsa_R_OF_1_4011:bool =
  high:bool((dsa_T_t1_1_4007:u32 ^ ~dsa_T_t2_1_4008:u32) &
            (dsa_T_t1_1_4007:u32 ^ dsa_R_EAX_32_1_4009:u32))
dsa_R_AF_1_4012:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_4009:u32 ^ dsa_T_t1_1_4007:u32 ^ dsa_T_t2_1_4008:u32))
dsa_R_PF_3_4015:bool =
  ~low:bool(let dsa_T_acc_1_4013:u32 :=
                                         dsa_R_EAX_32_1_4009:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_4009:u32 in
            let dsa_T_acc_2_4014:u32 :=
                                         dsa_T_acc_1_4013:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4013:u32 in
            dsa_T_acc_2_4014:u32 >> 1:u32 ^ dsa_T_acc_2_4014:u32)
dsa_R_SF_1_4016:bool = high:bool(dsa_R_EAX_32_1_4009:u32)
dsa_R_ZF_1_4017:bool = 0:u32 == dsa_R_EAX_32_1_4009:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0xa70d73, -1, u32, rw
  @context "R_EAX_32" = 0xa70d6e, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_4018:bool = false
dsa_T_t_1_4019:u32 = dsa_R_ECX_32_1_3956:u32
dsa_R_ECX_32_1_4020:u32 = dsa_R_ECX_32_1_3956:u32 - dsa_R_EAX_32_1_4009:u32
dsa_R_CF_1_4021:bool = dsa_T_t_1_4019:u32 < dsa_R_EAX_32_1_4009:u32
dsa_R_OF_1_4022:bool =
  high:bool((dsa_T_t_1_4019:u32 ^ dsa_R_EAX_32_1_4009:u32) &
            (dsa_T_t_1_4019:u32 ^ dsa_R_ECX_32_1_4020:u32))
dsa_R_AF_1_4023:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_4020:u32 ^ dsa_T_t_1_4019:u32 ^ dsa_R_EAX_32_1_4009:u32))
dsa_R_PF_3_4026:bool =
  ~low:bool(let dsa_T_acc_1_4024:u32 :=
                                         dsa_R_ECX_32_1_4020:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_4020:u32 in
            let dsa_T_acc_2_4025:u32 :=
                                         dsa_T_acc_1_4024:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4024:u32 in
            dsa_T_acc_2_4025:u32 >> 1:u32 ^ dsa_T_acc_2_4025:u32)
dsa_R_SF_1_4027:bool = high:bool(dsa_R_ECX_32_1_4020:u32)
dsa_R_ZF_1_4028:bool = 0:u32 == dsa_R_ECX_32_1_4020:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x10b48b, -1, u32, rd
  @context "R_EDX_32" = 0x10b48b, -1, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_4029:bool = false
dsa_T_t_1_4030:u32 = dsa_R_EDX_32_1_3996:u32 & dsa_R_EDX_32_1_3996:u32
dsa_R_OF_1_4031:bool = false
dsa_R_CF_1_4032:bool = false
dsa_R_AF_1_4033:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_4036:bool =
  ~low:bool(let dsa_T_acc_1_4034:u32 :=
                                         dsa_T_t_1_4030:u32 >> 4:u32 ^
                                         dsa_T_t_1_4030:u32 in
            let dsa_T_acc_2_4035:u32 :=
                                         dsa_T_acc_1_4034:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4034:u32 in
            dsa_T_acc_2_4035:u32 >> 1:u32 ^ dsa_T_acc_2_4035:u32)
dsa_R_SF_1_4037:bool = high:bool(dsa_T_t_1_4030:u32)
dsa_R_ZF_1_4038:bool = 0:u32 == dsa_T_t_1_4030:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0xa70d6e, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x5, -1, u32, rd
  @context "mem32[0xdd01cc65]" = 0x35, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc65_1_4039:u8 = low:u8(0x35:u8)
dsa_R_EDI_32_1_4040:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_4041:u32 = pad:u32(pad:u8(dsa_mem_dd01cc65_1_4039:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x5, -1, u32, wr
  @context "R_EDX_32" = 0x10b48b, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_4042:u32 = dsa_R_EDX_32_1_3996:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf067d, 0, u32, rd
  @context "R_EAX_32" = 0x35, -1, u32, rd
  @context "mem32[0xffaf067d]" = 0xa8, 0, u8, wr
label pc_0xdcf03221
dsa_mem_ffaf067d_1_4043:u8 = low:u8(0xa8:u8)
dsa_R_ESI_32_1_4044:u32 = 0xffaf067d:u32
dsa_mem_ffaf067d_1_4045:u8 = low:u8(low:u8(dsa_R_EAX_32_1_4041:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_4046:bool = false
dsa_R_EIP_1_4047:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_4038:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp113"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x35, -1, u32, wr
  @context "R_ECX_32" = 0x10b48b, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_4048:u32 = dsa_R_ECX_32_1_4042:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf067d, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_4049:u32 = 0xffaf067d:u32
dsa_R_DF_1_4050:bool = false
dsa_T_t_1_4051:u32 = dsa_R_ESI_32_1_4049:u32
dsa_R_ESI_32_1_4052:u32 = dsa_R_ESI_32_1_4049:u32 - 1:u32
dsa_R_CF_1_4053:bool = dsa_T_t_1_4051:u32 < 1:u32
dsa_R_OF_1_4054:bool =
  high:bool((dsa_T_t_1_4051:u32 ^ 1:u32) &
            (dsa_T_t_1_4051:u32 ^ dsa_R_ESI_32_1_4052:u32))
dsa_R_AF_1_4055:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_4052:u32 ^ dsa_T_t_1_4051:u32 ^ 1:u32))
dsa_R_PF_3_4058:bool =
  ~low:bool(let dsa_T_acc_1_4056:u32 :=
                                         dsa_R_ESI_32_1_4052:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_4052:u32 in
            let dsa_T_acc_2_4057:u32 :=
                                         dsa_T_acc_1_4056:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4056:u32 in
            dsa_T_acc_2_4057:u32 >> 1:u32 ^ dsa_T_acc_2_4057:u32)
dsa_R_SF_1_4059:bool = high:bool(dsa_R_ESI_32_1_4052:u32)
dsa_R_ZF_1_4060:bool = 0:u32 == dsa_R_ESI_32_1_4052:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x10b48b, -1, u32, rw
  @context "R_EDX_32" = 0x10b48b, -1, u32, wr
  @context "R_EFLAGS" = 0x282, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_4061:bool = false
dsa_R_EBP_32_1_4062:u32 = 0xcccccccd:u32
dsa_R_AF_1_4063:bool = false
dsa_R_OF_1_4064:bool = false
dsa_R_SF_1_4065:bool = true
dsa_R_DF_1_4066:bool = false
dsa_R_CF_1_4067:bool = false
dsa_R_EFLAGS_1_4068:u32 = 0x282:u32
dsa_R_PF_1_4069:bool = false
dsa_T_t_1_4070:u64 =
  pad:u64(dsa_R_EAX_32_1_4048:u32) * pad:u64(dsa_R_EBP_32_1_4062:u32)
dsa_R_EAX_32_1_4071:u32 = extract:31:0:[dsa_T_t_1_4070:u64]
dsa_R_EDX_32_1_4072:u32 = extract:63:32:[dsa_T_t_1_4070:u64]
dsa_R_OF_1_4073:bool = extract:63:32:[dsa_T_t_1_4070:u64] <> 0:u32
dsa_R_CF_1_4074:bool = extract:63:32:[dsa_T_t_1_4070:u64] <> 0:u32
dsa_R_SF_1_4075:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_4076:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_4077:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_4078:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0xd5d3c, -1, u32, rw
  @context "R_EFLAGS" = 0xa03, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_4079:bool = false
dsa_T_origDEST_1_4080:u32 = dsa_R_EDX_32_1_4072:u32
dsa_T_origCOUNT_1_4081:u32 = 3:u32
dsa_R_EDX_32_1_4082:u32 = dsa_R_EDX_32_1_4072:u32 >> 3:u32
dsa_R_CF_1_4083:bool =
  if dsa_T_origCOUNT_1_4081:u32 == 0:u32 then dsa_R_CF_1_4074:bool else
  high:bool(dsa_T_origDEST_1_4080:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_4081:u32)
dsa_R_OF_1_4084:bool =
  if dsa_T_origCOUNT_1_4081:u32 == 0:u32 then dsa_R_OF_1_4073:bool else
  if dsa_T_origCOUNT_1_4081:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_4080:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_4085:bool =
  if dsa_T_origCOUNT_1_4081:u32 == 0:u32 then dsa_R_SF_1_4075:bool else
  high:bool(dsa_R_EDX_32_1_4082:u32)
dsa_R_ZF_1_4086:bool =
  if dsa_T_origCOUNT_1_4081:u32 == 0:u32 then dsa_R_ZF_1_4076:bool else
  0:u32 == dsa_R_EDX_32_1_4082:u32
dsa_R_PF_3_4089:bool =
  if dsa_T_origCOUNT_1_4081:u32 == 0:u32 then dsa_R_PF_1_4078:bool else
  ~low:bool(let dsa_T_acc_1_4087:u32 :=
                                         dsa_R_EDX_32_1_4082:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_4082:u32 in
            let dsa_T_acc_2_4088:u32 :=
                                         dsa_T_acc_1_4087:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4087:u32 in
            dsa_T_acc_2_4088:u32 >> 1:u32 ^ dsa_T_acc_2_4088:u32)
dsa_R_AF_1_4090:bool =
  if dsa_T_origCOUNT_1_4081:u32 == 0:u32 then dsa_R_AF_1_4077:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x3574f, -1, u32, wr
  @context "R_EDX_32" = 0x1aba7, -1, u32, rd
  @context "R_EDX_32" = 0x1aba7, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_4091:u32 =
  dsa_R_EDX_32_1_4082:u32 + (dsa_R_EDX_32_1_4082:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x85a43, -1, u32, rw
  @context "R_EAX_32" = 0x85a43, -1, u32, rd
  @context "R_EFLAGS" = 0x203, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_4092:bool = false
dsa_T_t1_1_4093:u32 = dsa_R_EAX_32_1_4091:u32
dsa_T_t2_1_4094:u32 = dsa_R_EAX_32_1_4091:u32
dsa_R_EAX_32_1_4095:u32 = dsa_R_EAX_32_1_4091:u32 + dsa_T_t2_1_4094:u32
dsa_R_CF_1_4096:bool = dsa_R_EAX_32_1_4095:u32 < dsa_T_t1_1_4093:u32
dsa_R_OF_1_4097:bool =
  high:bool((dsa_T_t1_1_4093:u32 ^ ~dsa_T_t2_1_4094:u32) &
            (dsa_T_t1_1_4093:u32 ^ dsa_R_EAX_32_1_4095:u32))
dsa_R_AF_1_4098:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_4095:u32 ^ dsa_T_t1_1_4093:u32 ^ dsa_T_t2_1_4094:u32))
dsa_R_PF_3_4101:bool =
  ~low:bool(let dsa_T_acc_1_4099:u32 :=
                                         dsa_R_EAX_32_1_4095:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_4095:u32 in
            let dsa_T_acc_2_4100:u32 :=
                                         dsa_T_acc_1_4099:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4099:u32 in
            dsa_T_acc_2_4100:u32 >> 1:u32 ^ dsa_T_acc_2_4100:u32)
dsa_R_SF_1_4102:bool = high:bool(dsa_R_EAX_32_1_4095:u32)
dsa_R_ZF_1_4103:bool = 0:u32 == dsa_R_EAX_32_1_4095:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x10b48b, -1, u32, rw
  @context "R_EAX_32" = 0x10b486, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_4104:bool = false
dsa_T_t_1_4105:u32 = dsa_R_ECX_32_1_4042:u32
dsa_R_ECX_32_1_4106:u32 = dsa_R_ECX_32_1_4042:u32 - dsa_R_EAX_32_1_4095:u32
dsa_R_CF_1_4107:bool = dsa_T_t_1_4105:u32 < dsa_R_EAX_32_1_4095:u32
dsa_R_OF_1_4108:bool =
  high:bool((dsa_T_t_1_4105:u32 ^ dsa_R_EAX_32_1_4095:u32) &
            (dsa_T_t_1_4105:u32 ^ dsa_R_ECX_32_1_4106:u32))
dsa_R_AF_1_4109:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_4106:u32 ^ dsa_T_t_1_4105:u32 ^ dsa_R_EAX_32_1_4095:u32))
dsa_R_PF_3_4112:bool =
  ~low:bool(let dsa_T_acc_1_4110:u32 :=
                                         dsa_R_ECX_32_1_4106:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_4106:u32 in
            let dsa_T_acc_2_4111:u32 :=
                                         dsa_T_acc_1_4110:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4110:u32 in
            dsa_T_acc_2_4111:u32 >> 1:u32 ^ dsa_T_acc_2_4111:u32)
dsa_R_SF_1_4113:bool = high:bool(dsa_R_ECX_32_1_4106:u32)
dsa_R_ZF_1_4114:bool = 0:u32 == dsa_R_ECX_32_1_4106:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x1aba7, -1, u32, rd
  @context "R_EDX_32" = 0x1aba7, -1, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_4115:bool = false
dsa_T_t_1_4116:u32 = dsa_R_EDX_32_1_4082:u32 & dsa_R_EDX_32_1_4082:u32
dsa_R_OF_1_4117:bool = false
dsa_R_CF_1_4118:bool = false
dsa_R_AF_1_4119:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_4122:bool =
  ~low:bool(let dsa_T_acc_1_4120:u32 :=
                                         dsa_T_t_1_4116:u32 >> 4:u32 ^
                                         dsa_T_t_1_4116:u32 in
            let dsa_T_acc_2_4121:u32 :=
                                         dsa_T_acc_1_4120:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4120:u32 in
            dsa_T_acc_2_4121:u32 >> 1:u32 ^ dsa_T_acc_2_4121:u32)
dsa_R_SF_1_4123:bool = high:bool(dsa_T_t_1_4116:u32)
dsa_R_ZF_1_4124:bool = 0:u32 == dsa_T_t_1_4116:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x10b486, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x5, -1, u32, rd
  @context "mem32[0xdd01cc65]" = 0x35, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc65_1_4125:u8 = low:u8(0x35:u8)
dsa_R_EDI_32_1_4126:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_4127:u32 = pad:u32(pad:u8(dsa_mem_dd01cc65_1_4125:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x5, -1, u32, wr
  @context "R_EDX_32" = 0x1aba7, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_4128:u32 = dsa_R_EDX_32_1_4082:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf067c, 0, u32, rd
  @context "R_EAX_32" = 0x35, -1, u32, rd
  @context "mem32[0xffaf067c]" = 0x36, 0, u8, wr
label pc_0xdcf03221
dsa_mem_ffaf067c_1_4129:u8 = low:u8(0x36:u8)
dsa_R_ESI_32_1_4130:u32 = 0xffaf067c:u32
dsa_mem_ffaf067c_1_4131:u8 = low:u8(low:u8(dsa_R_EAX_32_1_4127:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_4132:bool = false
dsa_R_EIP_1_4133:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_4124:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp114"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x35, -1, u32, wr
  @context "R_ECX_32" = 0x1aba7, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_4134:u32 = dsa_R_ECX_32_1_4128:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf067c, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_4135:u32 = 0xffaf067c:u32
dsa_R_DF_1_4136:bool = false
dsa_T_t_1_4137:u32 = dsa_R_ESI_32_1_4135:u32
dsa_R_ESI_32_1_4138:u32 = dsa_R_ESI_32_1_4135:u32 - 1:u32
dsa_R_CF_1_4139:bool = dsa_T_t_1_4137:u32 < 1:u32
dsa_R_OF_1_4140:bool =
  high:bool((dsa_T_t_1_4137:u32 ^ 1:u32) &
            (dsa_T_t_1_4137:u32 ^ dsa_R_ESI_32_1_4138:u32))
dsa_R_AF_1_4141:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_4138:u32 ^ dsa_T_t_1_4137:u32 ^ 1:u32))
dsa_R_PF_3_4144:bool =
  ~low:bool(let dsa_T_acc_1_4142:u32 :=
                                         dsa_R_ESI_32_1_4138:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_4138:u32 in
            let dsa_T_acc_2_4143:u32 :=
                                         dsa_T_acc_1_4142:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4142:u32 in
            dsa_T_acc_2_4143:u32 >> 1:u32 ^ dsa_T_acc_2_4143:u32)
dsa_R_SF_1_4145:bool = high:bool(dsa_R_ESI_32_1_4138:u32)
dsa_R_ZF_1_4146:bool = 0:u32 == dsa_R_ESI_32_1_4138:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x1aba7, -1, u32, rw
  @context "R_EDX_32" = 0x1aba7, -1, u32, wr
  @context "R_EFLAGS" = 0x286, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_4147:bool = false
dsa_R_EBP_32_1_4148:u32 = 0xcccccccd:u32
dsa_R_AF_1_4149:bool = false
dsa_R_OF_1_4150:bool = false
dsa_R_SF_1_4151:bool = true
dsa_R_DF_1_4152:bool = false
dsa_R_CF_1_4153:bool = false
dsa_R_EFLAGS_1_4154:u32 = 0x286:u32
dsa_R_PF_1_4155:bool = true
dsa_T_t_1_4156:u64 =
  pad:u64(dsa_R_EAX_32_1_4134:u32) * pad:u64(dsa_R_EBP_32_1_4148:u32)
dsa_R_EAX_32_1_4157:u32 = extract:31:0:[dsa_T_t_1_4156:u64]
dsa_R_EDX_32_1_4158:u32 = extract:63:32:[dsa_T_t_1_4156:u64]
dsa_R_OF_1_4159:bool = extract:63:32:[dsa_T_t_1_4156:u64] <> 0:u32
dsa_R_CF_1_4160:bool = extract:63:32:[dsa_T_t_1_4156:u64] <> 0:u32
dsa_R_SF_1_4161:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_4162:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_4163:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_4164:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x1561f, -1, u32, rw
  @context "R_EFLAGS" = 0xa07, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_4165:bool = false
dsa_T_origDEST_1_4166:u32 = dsa_R_EDX_32_1_4158:u32
dsa_T_origCOUNT_1_4167:u32 = 3:u32
dsa_R_EDX_32_1_4168:u32 = dsa_R_EDX_32_1_4158:u32 >> 3:u32
dsa_R_CF_1_4169:bool =
  if dsa_T_origCOUNT_1_4167:u32 == 0:u32 then dsa_R_CF_1_4160:bool else
  high:bool(dsa_T_origDEST_1_4166:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_4167:u32)
dsa_R_OF_1_4170:bool =
  if dsa_T_origCOUNT_1_4167:u32 == 0:u32 then dsa_R_OF_1_4159:bool else
  if dsa_T_origCOUNT_1_4167:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_4166:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_4171:bool =
  if dsa_T_origCOUNT_1_4167:u32 == 0:u32 then dsa_R_SF_1_4161:bool else
  high:bool(dsa_R_EDX_32_1_4168:u32)
dsa_R_ZF_1_4172:bool =
  if dsa_T_origCOUNT_1_4167:u32 == 0:u32 then dsa_R_ZF_1_4162:bool else
  0:u32 == dsa_R_EDX_32_1_4168:u32
dsa_R_PF_3_4175:bool =
  if dsa_T_origCOUNT_1_4167:u32 == 0:u32 then dsa_R_PF_1_4164:bool else
  ~low:bool(let dsa_T_acc_1_4173:u32 :=
                                         dsa_R_EDX_32_1_4168:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_4168:u32 in
            let dsa_T_acc_2_4174:u32 :=
                                         dsa_T_acc_1_4173:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4173:u32 in
            dsa_T_acc_2_4174:u32 >> 1:u32 ^ dsa_T_acc_2_4174:u32)
dsa_R_AF_1_4176:bool =
  if dsa_T_origCOUNT_1_4167:u32 == 0:u32 then dsa_R_AF_1_4163:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x333388bb, -1, u32, wr
  @context "R_EDX_32" = 0x2ac3, -1, u32, rd
  @context "R_EDX_32" = 0x2ac3, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_4177:u32 =
  dsa_R_EDX_32_1_4168:u32 + (dsa_R_EDX_32_1_4168:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0xd5cf, -1, u32, rw
  @context "R_EAX_32" = 0xd5cf, -1, u32, rd
  @context "R_EFLAGS" = 0x207, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_4178:bool = false
dsa_T_t1_1_4179:u32 = dsa_R_EAX_32_1_4177:u32
dsa_T_t2_1_4180:u32 = dsa_R_EAX_32_1_4177:u32
dsa_R_EAX_32_1_4181:u32 = dsa_R_EAX_32_1_4177:u32 + dsa_T_t2_1_4180:u32
dsa_R_CF_1_4182:bool = dsa_R_EAX_32_1_4181:u32 < dsa_T_t1_1_4179:u32
dsa_R_OF_1_4183:bool =
  high:bool((dsa_T_t1_1_4179:u32 ^ ~dsa_T_t2_1_4180:u32) &
            (dsa_T_t1_1_4179:u32 ^ dsa_R_EAX_32_1_4181:u32))
dsa_R_AF_1_4184:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_4181:u32 ^ dsa_T_t1_1_4179:u32 ^ dsa_T_t2_1_4180:u32))
dsa_R_PF_3_4187:bool =
  ~low:bool(let dsa_T_acc_1_4185:u32 :=
                                         dsa_R_EAX_32_1_4181:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_4181:u32 in
            let dsa_T_acc_2_4186:u32 :=
                                         dsa_T_acc_1_4185:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4185:u32 in
            dsa_T_acc_2_4186:u32 >> 1:u32 ^ dsa_T_acc_2_4186:u32)
dsa_R_SF_1_4188:bool = high:bool(dsa_R_EAX_32_1_4181:u32)
dsa_R_ZF_1_4189:bool = 0:u32 == dsa_R_EAX_32_1_4181:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x1aba7, -1, u32, rw
  @context "R_EAX_32" = 0x1ab9e, -1, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_4190:bool = false
dsa_T_t_1_4191:u32 = dsa_R_ECX_32_1_4128:u32
dsa_R_ECX_32_1_4192:u32 = dsa_R_ECX_32_1_4128:u32 - dsa_R_EAX_32_1_4181:u32
dsa_R_CF_1_4193:bool = dsa_T_t_1_4191:u32 < dsa_R_EAX_32_1_4181:u32
dsa_R_OF_1_4194:bool =
  high:bool((dsa_T_t_1_4191:u32 ^ dsa_R_EAX_32_1_4181:u32) &
            (dsa_T_t_1_4191:u32 ^ dsa_R_ECX_32_1_4192:u32))
dsa_R_AF_1_4195:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_4192:u32 ^ dsa_T_t_1_4191:u32 ^ dsa_R_EAX_32_1_4181:u32))
dsa_R_PF_3_4198:bool =
  ~low:bool(let dsa_T_acc_1_4196:u32 :=
                                         dsa_R_ECX_32_1_4192:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_4192:u32 in
            let dsa_T_acc_2_4197:u32 :=
                                         dsa_T_acc_1_4196:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4196:u32 in
            dsa_T_acc_2_4197:u32 >> 1:u32 ^ dsa_T_acc_2_4197:u32)
dsa_R_SF_1_4199:bool = high:bool(dsa_R_ECX_32_1_4192:u32)
dsa_R_ZF_1_4200:bool = 0:u32 == dsa_R_ECX_32_1_4192:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x2ac3, -1, u32, rd
  @context "R_EDX_32" = 0x2ac3, -1, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_4201:bool = false
dsa_T_t_1_4202:u32 = dsa_R_EDX_32_1_4168:u32 & dsa_R_EDX_32_1_4168:u32
dsa_R_OF_1_4203:bool = false
dsa_R_CF_1_4204:bool = false
dsa_R_AF_1_4205:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_4208:bool =
  ~low:bool(let dsa_T_acc_1_4206:u32 :=
                                         dsa_T_t_1_4202:u32 >> 4:u32 ^
                                         dsa_T_t_1_4202:u32 in
            let dsa_T_acc_2_4207:u32 :=
                                         dsa_T_acc_1_4206:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4206:u32 in
            dsa_T_acc_2_4207:u32 >> 1:u32 ^ dsa_T_acc_2_4207:u32)
dsa_R_SF_1_4209:bool = high:bool(dsa_T_t_1_4202:u32)
dsa_R_ZF_1_4210:bool = 0:u32 == dsa_T_t_1_4202:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x1ab9e, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x9, -1, u32, rd
  @context "mem32[0xdd01cc69]" = 0x39, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc69_1_4211:u8 = low:u8(0x39:u8)
dsa_R_EDI_32_1_4212:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_4213:u32 = pad:u32(pad:u8(dsa_mem_dd01cc69_1_4211:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x9, -1, u32, wr
  @context "R_EDX_32" = 0x2ac3, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_4214:u32 = dsa_R_EDX_32_1_4168:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf067b, 0, u32, rd
  @context "R_EAX_32" = 0x39, -1, u32, rd
  @context "mem32[0xffaf067b]" = 0xf7, 0, u8, wr
label pc_0xdcf03221
dsa_mem_ffaf067b_1_4215:u8 = low:u8(-9:u8)
dsa_R_ESI_32_1_4216:u32 = 0xffaf067b:u32
dsa_mem_ffaf067b_1_4217:u8 = low:u8(low:u8(dsa_R_EAX_32_1_4213:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_4218:bool = false
dsa_R_EIP_1_4219:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_4210:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp115"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x39, -1, u32, wr
  @context "R_ECX_32" = 0x2ac3, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_4220:u32 = dsa_R_ECX_32_1_4214:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf067b, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_4221:u32 = 0xffaf067b:u32
dsa_R_DF_1_4222:bool = false
dsa_T_t_1_4223:u32 = dsa_R_ESI_32_1_4221:u32
dsa_R_ESI_32_1_4224:u32 = dsa_R_ESI_32_1_4221:u32 - 1:u32
dsa_R_CF_1_4225:bool = dsa_T_t_1_4223:u32 < 1:u32
dsa_R_OF_1_4226:bool =
  high:bool((dsa_T_t_1_4223:u32 ^ 1:u32) &
            (dsa_T_t_1_4223:u32 ^ dsa_R_ESI_32_1_4224:u32))
dsa_R_AF_1_4227:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_4224:u32 ^ dsa_T_t_1_4223:u32 ^ 1:u32))
dsa_R_PF_3_4230:bool =
  ~low:bool(let dsa_T_acc_1_4228:u32 :=
                                         dsa_R_ESI_32_1_4224:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_4224:u32 in
            let dsa_T_acc_2_4229:u32 :=
                                         dsa_T_acc_1_4228:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4228:u32 in
            dsa_T_acc_2_4229:u32 >> 1:u32 ^ dsa_T_acc_2_4229:u32)
dsa_R_SF_1_4231:bool = high:bool(dsa_R_ESI_32_1_4224:u32)
dsa_R_ZF_1_4232:bool = 0:u32 == dsa_R_ESI_32_1_4224:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x2ac3, -1, u32, rw
  @context "R_EDX_32" = 0x2ac3, -1, u32, wr
  @context "R_EFLAGS" = 0x282, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_4233:bool = false
dsa_R_EBP_32_1_4234:u32 = 0xcccccccd:u32
dsa_R_AF_1_4235:bool = false
dsa_R_OF_1_4236:bool = false
dsa_R_SF_1_4237:bool = true
dsa_R_DF_1_4238:bool = false
dsa_R_CF_1_4239:bool = false
dsa_R_EFLAGS_1_4240:u32 = 0x282:u32
dsa_R_PF_1_4241:bool = false
dsa_T_t_1_4242:u64 =
  pad:u64(dsa_R_EAX_32_1_4220:u32) * pad:u64(dsa_R_EBP_32_1_4234:u32)
dsa_R_EAX_32_1_4243:u32 = extract:31:0:[dsa_T_t_1_4242:u64]
dsa_R_EDX_32_1_4244:u32 = extract:63:32:[dsa_T_t_1_4242:u64]
dsa_R_OF_1_4245:bool = extract:63:32:[dsa_T_t_1_4242:u64] <> 0:u32
dsa_R_CF_1_4246:bool = extract:63:32:[dsa_T_t_1_4242:u64] <> 0:u32
dsa_R_SF_1_4247:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_4248:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_4249:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_4250:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x2235, -1, u32, rw
  @context "R_EFLAGS" = 0xa87, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_4251:bool = false
dsa_T_origDEST_1_4252:u32 = dsa_R_EDX_32_1_4244:u32
dsa_T_origCOUNT_1_4253:u32 = 3:u32
dsa_R_EDX_32_1_4254:u32 = dsa_R_EDX_32_1_4244:u32 >> 3:u32
dsa_R_CF_1_4255:bool =
  if dsa_T_origCOUNT_1_4253:u32 == 0:u32 then dsa_R_CF_1_4246:bool else
  high:bool(dsa_T_origDEST_1_4252:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_4253:u32)
dsa_R_OF_1_4256:bool =
  if dsa_T_origCOUNT_1_4253:u32 == 0:u32 then dsa_R_OF_1_4245:bool else
  if dsa_T_origCOUNT_1_4253:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_4252:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_4257:bool =
  if dsa_T_origCOUNT_1_4253:u32 == 0:u32 then dsa_R_SF_1_4247:bool else
  high:bool(dsa_R_EDX_32_1_4254:u32)
dsa_R_ZF_1_4258:bool =
  if dsa_T_origCOUNT_1_4253:u32 == 0:u32 then dsa_R_ZF_1_4248:bool else
  0:u32 == dsa_R_EDX_32_1_4254:u32
dsa_R_PF_3_4261:bool =
  if dsa_T_origCOUNT_1_4253:u32 == 0:u32 then dsa_R_PF_1_4250:bool else
  ~low:bool(let dsa_T_acc_1_4259:u32 :=
                                         dsa_R_EDX_32_1_4254:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_4254:u32 in
            let dsa_T_acc_2_4260:u32 :=
                                         dsa_T_acc_1_4259:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4259:u32 in
            dsa_T_acc_2_4260:u32 >> 1:u32 ^ dsa_T_acc_2_4260:u32)
dsa_R_AF_1_4262:bool =
  if dsa_T_origCOUNT_1_4253:u32 == 0:u32 then dsa_R_AF_1_4249:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x9999a227, -1, u32, wr
  @context "R_EDX_32" = 0x446, -1, u32, rd
  @context "R_EDX_32" = 0x446, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_4263:u32 =
  dsa_R_EDX_32_1_4254:u32 + (dsa_R_EDX_32_1_4254:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x155e, -1, u32, rw
  @context "R_EAX_32" = 0x155e, -1, u32, rd
  @context "R_EFLAGS" = 0x203, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_4264:bool = false
dsa_T_t1_1_4265:u32 = dsa_R_EAX_32_1_4263:u32
dsa_T_t2_1_4266:u32 = dsa_R_EAX_32_1_4263:u32
dsa_R_EAX_32_1_4267:u32 = dsa_R_EAX_32_1_4263:u32 + dsa_T_t2_1_4266:u32
dsa_R_CF_1_4268:bool = dsa_R_EAX_32_1_4267:u32 < dsa_T_t1_1_4265:u32
dsa_R_OF_1_4269:bool =
  high:bool((dsa_T_t1_1_4265:u32 ^ ~dsa_T_t2_1_4266:u32) &
            (dsa_T_t1_1_4265:u32 ^ dsa_R_EAX_32_1_4267:u32))
dsa_R_AF_1_4270:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_4267:u32 ^ dsa_T_t1_1_4265:u32 ^ dsa_T_t2_1_4266:u32))
dsa_R_PF_3_4273:bool =
  ~low:bool(let dsa_T_acc_1_4271:u32 :=
                                         dsa_R_EAX_32_1_4267:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_4267:u32 in
            let dsa_T_acc_2_4272:u32 :=
                                         dsa_T_acc_1_4271:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4271:u32 in
            dsa_T_acc_2_4272:u32 >> 1:u32 ^ dsa_T_acc_2_4272:u32)
dsa_R_SF_1_4274:bool = high:bool(dsa_R_EAX_32_1_4267:u32)
dsa_R_ZF_1_4275:bool = 0:u32 == dsa_R_EAX_32_1_4267:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x2ac3, -1, u32, rw
  @context "R_EAX_32" = 0x2abc, -1, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_4276:bool = false
dsa_T_t_1_4277:u32 = dsa_R_ECX_32_1_4214:u32
dsa_R_ECX_32_1_4278:u32 = dsa_R_ECX_32_1_4214:u32 - dsa_R_EAX_32_1_4267:u32
dsa_R_CF_1_4279:bool = dsa_T_t_1_4277:u32 < dsa_R_EAX_32_1_4267:u32
dsa_R_OF_1_4280:bool =
  high:bool((dsa_T_t_1_4277:u32 ^ dsa_R_EAX_32_1_4267:u32) &
            (dsa_T_t_1_4277:u32 ^ dsa_R_ECX_32_1_4278:u32))
dsa_R_AF_1_4281:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_4278:u32 ^ dsa_T_t_1_4277:u32 ^ dsa_R_EAX_32_1_4267:u32))
dsa_R_PF_3_4284:bool =
  ~low:bool(let dsa_T_acc_1_4282:u32 :=
                                         dsa_R_ECX_32_1_4278:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_4278:u32 in
            let dsa_T_acc_2_4283:u32 :=
                                         dsa_T_acc_1_4282:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4282:u32 in
            dsa_T_acc_2_4283:u32 >> 1:u32 ^ dsa_T_acc_2_4283:u32)
dsa_R_SF_1_4285:bool = high:bool(dsa_R_ECX_32_1_4278:u32)
dsa_R_ZF_1_4286:bool = 0:u32 == dsa_R_ECX_32_1_4278:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x446, -1, u32, rd
  @context "R_EDX_32" = 0x446, -1, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_4287:bool = false
dsa_T_t_1_4288:u32 = dsa_R_EDX_32_1_4254:u32 & dsa_R_EDX_32_1_4254:u32
dsa_R_OF_1_4289:bool = false
dsa_R_CF_1_4290:bool = false
dsa_R_AF_1_4291:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_4294:bool =
  ~low:bool(let dsa_T_acc_1_4292:u32 :=
                                         dsa_T_t_1_4288:u32 >> 4:u32 ^
                                         dsa_T_t_1_4288:u32 in
            let dsa_T_acc_2_4293:u32 :=
                                         dsa_T_acc_1_4292:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4292:u32 in
            dsa_T_acc_2_4293:u32 >> 1:u32 ^ dsa_T_acc_2_4293:u32)
dsa_R_SF_1_4295:bool = high:bool(dsa_T_t_1_4288:u32)
dsa_R_ZF_1_4296:bool = 0:u32 == dsa_T_t_1_4288:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x2abc, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x7, -1, u32, rd
  @context "mem32[0xdd01cc67]" = 0x37, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc67_1_4297:u8 = low:u8(0x37:u8)
dsa_R_EDI_32_1_4298:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_4299:u32 = pad:u32(pad:u8(dsa_mem_dd01cc67_1_4297:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x7, -1, u32, wr
  @context "R_EDX_32" = 0x446, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_4300:u32 = dsa_R_EDX_32_1_4254:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf067a, 0, u32, rd
  @context "R_EAX_32" = 0x37, -1, u32, rd
  @context "mem32[0xffaf067a]" = 0x70, 0, u8, wr
label pc_0xdcf03221
dsa_mem_ffaf067a_1_4301:u8 = low:u8(0x70:u8)
dsa_R_ESI_32_1_4302:u32 = 0xffaf067a:u32
dsa_mem_ffaf067a_1_4303:u8 = low:u8(low:u8(dsa_R_EAX_32_1_4299:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_4304:bool = false
dsa_R_EIP_1_4305:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_4296:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp116"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x37, -1, u32, wr
  @context "R_ECX_32" = 0x446, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_4306:u32 = dsa_R_ECX_32_1_4300:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf067a, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_4307:u32 = 0xffaf067a:u32
dsa_R_DF_1_4308:bool = false
dsa_T_t_1_4309:u32 = dsa_R_ESI_32_1_4307:u32
dsa_R_ESI_32_1_4310:u32 = dsa_R_ESI_32_1_4307:u32 - 1:u32
dsa_R_CF_1_4311:bool = dsa_T_t_1_4309:u32 < 1:u32
dsa_R_OF_1_4312:bool =
  high:bool((dsa_T_t_1_4309:u32 ^ 1:u32) &
            (dsa_T_t_1_4309:u32 ^ dsa_R_ESI_32_1_4310:u32))
dsa_R_AF_1_4313:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_4310:u32 ^ dsa_T_t_1_4309:u32 ^ 1:u32))
dsa_R_PF_3_4316:bool =
  ~low:bool(let dsa_T_acc_1_4314:u32 :=
                                         dsa_R_ESI_32_1_4310:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_4310:u32 in
            let dsa_T_acc_2_4315:u32 :=
                                         dsa_T_acc_1_4314:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4314:u32 in
            dsa_T_acc_2_4315:u32 >> 1:u32 ^ dsa_T_acc_2_4315:u32)
dsa_R_SF_1_4317:bool = high:bool(dsa_R_ESI_32_1_4310:u32)
dsa_R_ZF_1_4318:bool = 0:u32 == dsa_R_ESI_32_1_4310:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x446, -1, u32, rw
  @context "R_EDX_32" = 0x446, -1, u32, wr
  @context "R_EFLAGS" = 0x282, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_4319:bool = false
dsa_R_EBP_32_1_4320:u32 = 0xcccccccd:u32
dsa_R_AF_1_4321:bool = false
dsa_R_OF_1_4322:bool = false
dsa_R_SF_1_4323:bool = true
dsa_R_DF_1_4324:bool = false
dsa_R_CF_1_4325:bool = false
dsa_R_EFLAGS_1_4326:u32 = 0x282:u32
dsa_R_PF_1_4327:bool = false
dsa_T_t_1_4328:u64 =
  pad:u64(dsa_R_EAX_32_1_4306:u32) * pad:u64(dsa_R_EBP_32_1_4320:u32)
dsa_R_EAX_32_1_4329:u32 = extract:31:0:[dsa_T_t_1_4328:u64]
dsa_R_EDX_32_1_4330:u32 = extract:63:32:[dsa_T_t_1_4328:u64]
dsa_R_OF_1_4331:bool = extract:63:32:[dsa_T_t_1_4328:u64] <> 0:u32
dsa_R_CF_1_4332:bool = extract:63:32:[dsa_T_t_1_4328:u64] <> 0:u32
dsa_R_SF_1_4333:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_4334:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_4335:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_4336:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x36b, -1, u32, rw
  @context "R_EFLAGS" = 0xa03, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_4337:bool = false
dsa_T_origDEST_1_4338:u32 = dsa_R_EDX_32_1_4330:u32
dsa_T_origCOUNT_1_4339:u32 = 3:u32
dsa_R_EDX_32_1_4340:u32 = dsa_R_EDX_32_1_4330:u32 >> 3:u32
dsa_R_CF_1_4341:bool =
  if dsa_T_origCOUNT_1_4339:u32 == 0:u32 then dsa_R_CF_1_4332:bool else
  high:bool(dsa_T_origDEST_1_4338:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_4339:u32)
dsa_R_OF_1_4342:bool =
  if dsa_T_origCOUNT_1_4339:u32 == 0:u32 then dsa_R_OF_1_4331:bool else
  if dsa_T_origCOUNT_1_4339:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_4338:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_4343:bool =
  if dsa_T_origCOUNT_1_4339:u32 == 0:u32 then dsa_R_SF_1_4333:bool else
  high:bool(dsa_R_EDX_32_1_4340:u32)
dsa_R_ZF_1_4344:bool =
  if dsa_T_origCOUNT_1_4339:u32 == 0:u32 then dsa_R_ZF_1_4334:bool else
  0:u32 == dsa_R_EDX_32_1_4340:u32
dsa_R_PF_3_4347:bool =
  if dsa_T_origCOUNT_1_4339:u32 == 0:u32 then dsa_R_PF_1_4336:bool else
  ~low:bool(let dsa_T_acc_1_4345:u32 :=
                                         dsa_R_EDX_32_1_4340:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_4340:u32 in
            let dsa_T_acc_2_4346:u32 :=
                                         dsa_T_acc_1_4345:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4345:u32 in
            dsa_T_acc_2_4346:u32 >> 1:u32 ^ dsa_T_acc_2_4346:u32)
dsa_R_AF_1_4348:bool =
  if dsa_T_origCOUNT_1_4339:u32 == 0:u32 then dsa_R_AF_1_4335:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x3333340e, -1, u32, wr
  @context "R_EDX_32" = 0x6d, -1, u32, rd
  @context "R_EDX_32" = 0x6d, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_4349:u32 =
  dsa_R_EDX_32_1_4340:u32 + (dsa_R_EDX_32_1_4340:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x221, -1, u32, rw
  @context "R_EAX_32" = 0x221, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_4350:bool = false
dsa_T_t1_1_4351:u32 = dsa_R_EAX_32_1_4349:u32
dsa_T_t2_1_4352:u32 = dsa_R_EAX_32_1_4349:u32
dsa_R_EAX_32_1_4353:u32 = dsa_R_EAX_32_1_4349:u32 + dsa_T_t2_1_4352:u32
dsa_R_CF_1_4354:bool = dsa_R_EAX_32_1_4353:u32 < dsa_T_t1_1_4351:u32
dsa_R_OF_1_4355:bool =
  high:bool((dsa_T_t1_1_4351:u32 ^ ~dsa_T_t2_1_4352:u32) &
            (dsa_T_t1_1_4351:u32 ^ dsa_R_EAX_32_1_4353:u32))
dsa_R_AF_1_4356:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_4353:u32 ^ dsa_T_t1_1_4351:u32 ^ dsa_T_t2_1_4352:u32))
dsa_R_PF_3_4359:bool =
  ~low:bool(let dsa_T_acc_1_4357:u32 :=
                                         dsa_R_EAX_32_1_4353:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_4353:u32 in
            let dsa_T_acc_2_4358:u32 :=
                                         dsa_T_acc_1_4357:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4357:u32 in
            dsa_T_acc_2_4358:u32 >> 1:u32 ^ dsa_T_acc_2_4358:u32)
dsa_R_SF_1_4360:bool = high:bool(dsa_R_EAX_32_1_4353:u32)
dsa_R_ZF_1_4361:bool = 0:u32 == dsa_R_EAX_32_1_4353:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x446, -1, u32, rw
  @context "R_EAX_32" = 0x442, -1, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_4362:bool = false
dsa_T_t_1_4363:u32 = dsa_R_ECX_32_1_4300:u32
dsa_R_ECX_32_1_4364:u32 = dsa_R_ECX_32_1_4300:u32 - dsa_R_EAX_32_1_4353:u32
dsa_R_CF_1_4365:bool = dsa_T_t_1_4363:u32 < dsa_R_EAX_32_1_4353:u32
dsa_R_OF_1_4366:bool =
  high:bool((dsa_T_t_1_4363:u32 ^ dsa_R_EAX_32_1_4353:u32) &
            (dsa_T_t_1_4363:u32 ^ dsa_R_ECX_32_1_4364:u32))
dsa_R_AF_1_4367:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_4364:u32 ^ dsa_T_t_1_4363:u32 ^ dsa_R_EAX_32_1_4353:u32))
dsa_R_PF_3_4370:bool =
  ~low:bool(let dsa_T_acc_1_4368:u32 :=
                                         dsa_R_ECX_32_1_4364:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_4364:u32 in
            let dsa_T_acc_2_4369:u32 :=
                                         dsa_T_acc_1_4368:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4368:u32 in
            dsa_T_acc_2_4369:u32 >> 1:u32 ^ dsa_T_acc_2_4369:u32)
dsa_R_SF_1_4371:bool = high:bool(dsa_R_ECX_32_1_4364:u32)
dsa_R_ZF_1_4372:bool = 0:u32 == dsa_R_ECX_32_1_4364:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x6d, -1, u32, rd
  @context "R_EDX_32" = 0x6d, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_4373:bool = false
dsa_T_t_1_4374:u32 = dsa_R_EDX_32_1_4340:u32 & dsa_R_EDX_32_1_4340:u32
dsa_R_OF_1_4375:bool = false
dsa_R_CF_1_4376:bool = false
dsa_R_AF_1_4377:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_4380:bool =
  ~low:bool(let dsa_T_acc_1_4378:u32 :=
                                         dsa_T_t_1_4374:u32 >> 4:u32 ^
                                         dsa_T_t_1_4374:u32 in
            let dsa_T_acc_2_4379:u32 :=
                                         dsa_T_acc_1_4378:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4378:u32 in
            dsa_T_acc_2_4379:u32 >> 1:u32 ^ dsa_T_acc_2_4379:u32)
dsa_R_SF_1_4381:bool = high:bool(dsa_T_t_1_4374:u32)
dsa_R_ZF_1_4382:bool = 0:u32 == dsa_T_t_1_4374:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x442, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x4, -1, u32, rd
  @context "mem32[0xdd01cc64]" = 0x34, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc64_1_4383:u8 = low:u8(0x34:u8)
dsa_R_EDI_32_1_4384:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_4385:u32 = pad:u32(pad:u8(dsa_mem_dd01cc64_1_4383:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x4, -1, u32, wr
  @context "R_EDX_32" = 0x6d, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_4386:u32 = dsa_R_EDX_32_1_4340:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf0679, 0, u32, rd
  @context "R_EAX_32" = 0x34, -1, u32, rd
  @context "mem32[0xffaf0679]" = 0xb9, 0, u8, wr
label pc_0xdcf03221
dsa_mem_ffaf0679_1_4387:u8 = low:u8(0xb9:u8)
dsa_R_ESI_32_1_4388:u32 = 0xffaf0679:u32
dsa_mem_ffaf0679_1_4389:u8 = low:u8(low:u8(dsa_R_EAX_32_1_4385:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_4390:bool = false
dsa_R_EIP_1_4391:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_4382:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp117"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x34, -1, u32, wr
  @context "R_ECX_32" = 0x6d, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_4392:u32 = dsa_R_ECX_32_1_4386:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf0679, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_4393:u32 = 0xffaf0679:u32
dsa_R_DF_1_4394:bool = false
dsa_T_t_1_4395:u32 = dsa_R_ESI_32_1_4393:u32
dsa_R_ESI_32_1_4396:u32 = dsa_R_ESI_32_1_4393:u32 - 1:u32
dsa_R_CF_1_4397:bool = dsa_T_t_1_4395:u32 < 1:u32
dsa_R_OF_1_4398:bool =
  high:bool((dsa_T_t_1_4395:u32 ^ 1:u32) &
            (dsa_T_t_1_4395:u32 ^ dsa_R_ESI_32_1_4396:u32))
dsa_R_AF_1_4399:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_4396:u32 ^ dsa_T_t_1_4395:u32 ^ 1:u32))
dsa_R_PF_3_4402:bool =
  ~low:bool(let dsa_T_acc_1_4400:u32 :=
                                         dsa_R_ESI_32_1_4396:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_4396:u32 in
            let dsa_T_acc_2_4401:u32 :=
                                         dsa_T_acc_1_4400:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4400:u32 in
            dsa_T_acc_2_4401:u32 >> 1:u32 ^ dsa_T_acc_2_4401:u32)
dsa_R_SF_1_4403:bool = high:bool(dsa_R_ESI_32_1_4396:u32)
dsa_R_ZF_1_4404:bool = 0:u32 == dsa_R_ESI_32_1_4396:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x6d, -1, u32, rw
  @context "R_EDX_32" = 0x6d, -1, u32, wr
  @context "R_EFLAGS" = 0x286, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_4405:bool = false
dsa_R_EBP_32_1_4406:u32 = 0xcccccccd:u32
dsa_R_AF_1_4407:bool = false
dsa_R_OF_1_4408:bool = false
dsa_R_SF_1_4409:bool = true
dsa_R_DF_1_4410:bool = false
dsa_R_CF_1_4411:bool = false
dsa_R_EFLAGS_1_4412:u32 = 0x286:u32
dsa_R_PF_1_4413:bool = true
dsa_T_t_1_4414:u64 =
  pad:u64(dsa_R_EAX_32_1_4392:u32) * pad:u64(dsa_R_EBP_32_1_4406:u32)
dsa_R_EAX_32_1_4415:u32 = extract:31:0:[dsa_T_t_1_4414:u64]
dsa_R_EDX_32_1_4416:u32 = extract:63:32:[dsa_T_t_1_4414:u64]
dsa_R_OF_1_4417:bool = extract:63:32:[dsa_T_t_1_4414:u64] <> 0:u32
dsa_R_CF_1_4418:bool = extract:63:32:[dsa_T_t_1_4414:u64] <> 0:u32
dsa_R_SF_1_4419:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_4420:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_4421:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_4422:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x57, -1, u32, rw
  @context "R_EFLAGS" = 0xa03, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_4423:bool = false
dsa_T_origDEST_1_4424:u32 = dsa_R_EDX_32_1_4416:u32
dsa_T_origCOUNT_1_4425:u32 = 3:u32
dsa_R_EDX_32_1_4426:u32 = dsa_R_EDX_32_1_4416:u32 >> 3:u32
dsa_R_CF_1_4427:bool =
  if dsa_T_origCOUNT_1_4425:u32 == 0:u32 then dsa_R_CF_1_4418:bool else
  high:bool(dsa_T_origDEST_1_4424:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_4425:u32)
dsa_R_OF_1_4428:bool =
  if dsa_T_origCOUNT_1_4425:u32 == 0:u32 then dsa_R_OF_1_4417:bool else
  if dsa_T_origCOUNT_1_4425:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_4424:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_4429:bool =
  if dsa_T_origCOUNT_1_4425:u32 == 0:u32 then dsa_R_SF_1_4419:bool else
  high:bool(dsa_R_EDX_32_1_4426:u32)
dsa_R_ZF_1_4430:bool =
  if dsa_T_origCOUNT_1_4425:u32 == 0:u32 then dsa_R_ZF_1_4420:bool else
  0:u32 == dsa_R_EDX_32_1_4426:u32
dsa_R_PF_3_4433:bool =
  if dsa_T_origCOUNT_1_4425:u32 == 0:u32 then dsa_R_PF_1_4422:bool else
  ~low:bool(let dsa_T_acc_1_4431:u32 :=
                                         dsa_R_EDX_32_1_4426:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_4426:u32 in
            let dsa_T_acc_2_4432:u32 :=
                                         dsa_T_acc_1_4431:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4431:u32 in
            dsa_T_acc_2_4432:u32 >> 1:u32 ^ dsa_T_acc_2_4432:u32)
dsa_R_AF_1_4434:bool =
  if dsa_T_origCOUNT_1_4425:u32 == 0:u32 then dsa_R_AF_1_4421:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x33333349, -1, u32, wr
  @context "R_EDX_32" = 0xa, -1, u32, rd
  @context "R_EDX_32" = 0xa, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_4435:u32 =
  dsa_R_EDX_32_1_4426:u32 + (dsa_R_EDX_32_1_4426:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x32, -1, u32, rw
  @context "R_EAX_32" = 0x32, -1, u32, rd
  @context "R_EFLAGS" = 0x207, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_4436:bool = false
dsa_T_t1_1_4437:u32 = dsa_R_EAX_32_1_4435:u32
dsa_T_t2_1_4438:u32 = dsa_R_EAX_32_1_4435:u32
dsa_R_EAX_32_1_4439:u32 = dsa_R_EAX_32_1_4435:u32 + dsa_T_t2_1_4438:u32
dsa_R_CF_1_4440:bool = dsa_R_EAX_32_1_4439:u32 < dsa_T_t1_1_4437:u32
dsa_R_OF_1_4441:bool =
  high:bool((dsa_T_t1_1_4437:u32 ^ ~dsa_T_t2_1_4438:u32) &
            (dsa_T_t1_1_4437:u32 ^ dsa_R_EAX_32_1_4439:u32))
dsa_R_AF_1_4442:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_4439:u32 ^ dsa_T_t1_1_4437:u32 ^ dsa_T_t2_1_4438:u32))
dsa_R_PF_3_4445:bool =
  ~low:bool(let dsa_T_acc_1_4443:u32 :=
                                         dsa_R_EAX_32_1_4439:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_4439:u32 in
            let dsa_T_acc_2_4444:u32 :=
                                         dsa_T_acc_1_4443:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4443:u32 in
            dsa_T_acc_2_4444:u32 >> 1:u32 ^ dsa_T_acc_2_4444:u32)
dsa_R_SF_1_4446:bool = high:bool(dsa_R_EAX_32_1_4439:u32)
dsa_R_ZF_1_4447:bool = 0:u32 == dsa_R_EAX_32_1_4439:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x6d, -1, u32, rw
  @context "R_EAX_32" = 0x64, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_4448:bool = false
dsa_T_t_1_4449:u32 = dsa_R_ECX_32_1_4386:u32
dsa_R_ECX_32_1_4450:u32 = dsa_R_ECX_32_1_4386:u32 - dsa_R_EAX_32_1_4439:u32
dsa_R_CF_1_4451:bool = dsa_T_t_1_4449:u32 < dsa_R_EAX_32_1_4439:u32
dsa_R_OF_1_4452:bool =
  high:bool((dsa_T_t_1_4449:u32 ^ dsa_R_EAX_32_1_4439:u32) &
            (dsa_T_t_1_4449:u32 ^ dsa_R_ECX_32_1_4450:u32))
dsa_R_AF_1_4453:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_4450:u32 ^ dsa_T_t_1_4449:u32 ^ dsa_R_EAX_32_1_4439:u32))
dsa_R_PF_3_4456:bool =
  ~low:bool(let dsa_T_acc_1_4454:u32 :=
                                         dsa_R_ECX_32_1_4450:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_4450:u32 in
            let dsa_T_acc_2_4455:u32 :=
                                         dsa_T_acc_1_4454:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4454:u32 in
            dsa_T_acc_2_4455:u32 >> 1:u32 ^ dsa_T_acc_2_4455:u32)
dsa_R_SF_1_4457:bool = high:bool(dsa_R_ECX_32_1_4450:u32)
dsa_R_ZF_1_4458:bool = 0:u32 == dsa_R_ECX_32_1_4450:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0xa, -1, u32, rd
  @context "R_EDX_32" = 0xa, -1, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_4459:bool = false
dsa_T_t_1_4460:u32 = dsa_R_EDX_32_1_4426:u32 & dsa_R_EDX_32_1_4426:u32
dsa_R_OF_1_4461:bool = false
dsa_R_CF_1_4462:bool = false
dsa_R_AF_1_4463:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_4466:bool =
  ~low:bool(let dsa_T_acc_1_4464:u32 :=
                                         dsa_T_t_1_4460:u32 >> 4:u32 ^
                                         dsa_T_t_1_4460:u32 in
            let dsa_T_acc_2_4465:u32 :=
                                         dsa_T_acc_1_4464:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4464:u32 in
            dsa_T_acc_2_4465:u32 >> 1:u32 ^ dsa_T_acc_2_4465:u32)
dsa_R_SF_1_4467:bool = high:bool(dsa_T_t_1_4460:u32)
dsa_R_ZF_1_4468:bool = 0:u32 == dsa_T_t_1_4460:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x64, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x9, -1, u32, rd
  @context "mem32[0xdd01cc69]" = 0x39, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc69_1_4469:u8 = low:u8(0x39:u8)
dsa_R_EDI_32_1_4470:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_4471:u32 = pad:u32(pad:u8(dsa_mem_dd01cc69_1_4469:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x9, -1, u32, wr
  @context "R_EDX_32" = 0xa, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_4472:u32 = dsa_R_EDX_32_1_4426:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf0678, 0, u32, rd
  @context "R_EAX_32" = 0x39, -1, u32, rd
  @context "mem32[0xffaf0678]" = 0x38, 0, u8, wr
label pc_0xdcf03221
dsa_mem_ffaf0678_1_4473:u8 = low:u8(0x38:u8)
dsa_R_ESI_32_1_4474:u32 = 0xffaf0678:u32
dsa_mem_ffaf0678_1_4475:u8 = low:u8(low:u8(dsa_R_EAX_32_1_4471:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_4476:bool = false
dsa_R_EIP_1_4477:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_4468:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp118"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x39, -1, u32, wr
  @context "R_ECX_32" = 0xa, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_4478:u32 = dsa_R_ECX_32_1_4472:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf0678, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_4479:u32 = 0xffaf0678:u32
dsa_R_DF_1_4480:bool = false
dsa_T_t_1_4481:u32 = dsa_R_ESI_32_1_4479:u32
dsa_R_ESI_32_1_4482:u32 = dsa_R_ESI_32_1_4479:u32 - 1:u32
dsa_R_CF_1_4483:bool = dsa_T_t_1_4481:u32 < 1:u32
dsa_R_OF_1_4484:bool =
  high:bool((dsa_T_t_1_4481:u32 ^ 1:u32) &
            (dsa_T_t_1_4481:u32 ^ dsa_R_ESI_32_1_4482:u32))
dsa_R_AF_1_4485:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_4482:u32 ^ dsa_T_t_1_4481:u32 ^ 1:u32))
dsa_R_PF_3_4488:bool =
  ~low:bool(let dsa_T_acc_1_4486:u32 :=
                                         dsa_R_ESI_32_1_4482:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_4482:u32 in
            let dsa_T_acc_2_4487:u32 :=
                                         dsa_T_acc_1_4486:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4486:u32 in
            dsa_T_acc_2_4487:u32 >> 1:u32 ^ dsa_T_acc_2_4487:u32)
dsa_R_SF_1_4489:bool = high:bool(dsa_R_ESI_32_1_4482:u32)
dsa_R_ZF_1_4490:bool = 0:u32 == dsa_R_ESI_32_1_4482:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0xa, -1, u32, rw
  @context "R_EDX_32" = 0xa, -1, u32, wr
  @context "R_EFLAGS" = 0x286, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_4491:bool = false
dsa_R_EBP_32_1_4492:u32 = 0xcccccccd:u32
dsa_R_AF_1_4493:bool = false
dsa_R_OF_1_4494:bool = false
dsa_R_SF_1_4495:bool = true
dsa_R_DF_1_4496:bool = false
dsa_R_CF_1_4497:bool = false
dsa_R_EFLAGS_1_4498:u32 = 0x286:u32
dsa_R_PF_1_4499:bool = true
dsa_T_t_1_4500:u64 =
  pad:u64(dsa_R_EAX_32_1_4478:u32) * pad:u64(dsa_R_EBP_32_1_4492:u32)
dsa_R_EAX_32_1_4501:u32 = extract:31:0:[dsa_T_t_1_4500:u64]
dsa_R_EDX_32_1_4502:u32 = extract:63:32:[dsa_T_t_1_4500:u64]
dsa_R_OF_1_4503:bool = extract:63:32:[dsa_T_t_1_4500:u64] <> 0:u32
dsa_R_CF_1_4504:bool = extract:63:32:[dsa_T_t_1_4500:u64] <> 0:u32
dsa_R_SF_1_4505:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_4506:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_4507:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_4508:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x8, -1, u32, rw
  @context "R_EFLAGS" = 0xa03, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_4509:bool = false
dsa_T_origDEST_1_4510:u32 = dsa_R_EDX_32_1_4502:u32
dsa_T_origCOUNT_1_4511:u32 = 3:u32
dsa_R_EDX_32_1_4512:u32 = dsa_R_EDX_32_1_4502:u32 >> 3:u32
dsa_R_CF_1_4513:bool =
  if dsa_T_origCOUNT_1_4511:u32 == 0:u32 then dsa_R_CF_1_4504:bool else
  high:bool(dsa_T_origDEST_1_4510:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_4511:u32)
dsa_R_OF_1_4514:bool =
  if dsa_T_origCOUNT_1_4511:u32 == 0:u32 then dsa_R_OF_1_4503:bool else
  if dsa_T_origCOUNT_1_4511:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_4510:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_4515:bool =
  if dsa_T_origCOUNT_1_4511:u32 == 0:u32 then dsa_R_SF_1_4505:bool else
  high:bool(dsa_R_EDX_32_1_4512:u32)
dsa_R_ZF_1_4516:bool =
  if dsa_T_origCOUNT_1_4511:u32 == 0:u32 then dsa_R_ZF_1_4506:bool else
  0:u32 == dsa_R_EDX_32_1_4512:u32
dsa_R_PF_3_4519:bool =
  if dsa_T_origCOUNT_1_4511:u32 == 0:u32 then dsa_R_PF_1_4508:bool else
  ~low:bool(let dsa_T_acc_1_4517:u32 :=
                                         dsa_R_EDX_32_1_4512:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_4512:u32 in
            let dsa_T_acc_2_4518:u32 :=
                                         dsa_T_acc_1_4517:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4517:u32 in
            dsa_T_acc_2_4518:u32 >> 1:u32 ^ dsa_T_acc_2_4518:u32)
dsa_R_AF_1_4520:bool =
  if dsa_T_origCOUNT_1_4511:u32 == 0:u32 then dsa_R_AF_1_4507:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x2, -1, u32, wr
  @context "R_EDX_32" = 0x1, -1, u32, rd
  @context "R_EDX_32" = 0x1, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_4521:u32 =
  dsa_R_EDX_32_1_4512:u32 + (dsa_R_EDX_32_1_4512:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x5, -1, u32, rw
  @context "R_EAX_32" = 0x5, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_4522:bool = false
dsa_T_t1_1_4523:u32 = dsa_R_EAX_32_1_4521:u32
dsa_T_t2_1_4524:u32 = dsa_R_EAX_32_1_4521:u32
dsa_R_EAX_32_1_4525:u32 = dsa_R_EAX_32_1_4521:u32 + dsa_T_t2_1_4524:u32
dsa_R_CF_1_4526:bool = dsa_R_EAX_32_1_4525:u32 < dsa_T_t1_1_4523:u32
dsa_R_OF_1_4527:bool =
  high:bool((dsa_T_t1_1_4523:u32 ^ ~dsa_T_t2_1_4524:u32) &
            (dsa_T_t1_1_4523:u32 ^ dsa_R_EAX_32_1_4525:u32))
dsa_R_AF_1_4528:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_4525:u32 ^ dsa_T_t1_1_4523:u32 ^ dsa_T_t2_1_4524:u32))
dsa_R_PF_3_4531:bool =
  ~low:bool(let dsa_T_acc_1_4529:u32 :=
                                         dsa_R_EAX_32_1_4525:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_4525:u32 in
            let dsa_T_acc_2_4530:u32 :=
                                         dsa_T_acc_1_4529:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4529:u32 in
            dsa_T_acc_2_4530:u32 >> 1:u32 ^ dsa_T_acc_2_4530:u32)
dsa_R_SF_1_4532:bool = high:bool(dsa_R_EAX_32_1_4525:u32)
dsa_R_ZF_1_4533:bool = 0:u32 == dsa_R_EAX_32_1_4525:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0xa, -1, u32, rw
  @context "R_EAX_32" = 0xa, -1, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_4534:bool = false
dsa_T_t_1_4535:u32 = dsa_R_ECX_32_1_4472:u32
dsa_R_ECX_32_1_4536:u32 = dsa_R_ECX_32_1_4472:u32 - dsa_R_EAX_32_1_4525:u32
dsa_R_CF_1_4537:bool = dsa_T_t_1_4535:u32 < dsa_R_EAX_32_1_4525:u32
dsa_R_OF_1_4538:bool =
  high:bool((dsa_T_t_1_4535:u32 ^ dsa_R_EAX_32_1_4525:u32) &
            (dsa_T_t_1_4535:u32 ^ dsa_R_ECX_32_1_4536:u32))
dsa_R_AF_1_4539:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_4536:u32 ^ dsa_T_t_1_4535:u32 ^ dsa_R_EAX_32_1_4525:u32))
dsa_R_PF_3_4542:bool =
  ~low:bool(let dsa_T_acc_1_4540:u32 :=
                                         dsa_R_ECX_32_1_4536:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_4536:u32 in
            let dsa_T_acc_2_4541:u32 :=
                                         dsa_T_acc_1_4540:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4540:u32 in
            dsa_T_acc_2_4541:u32 >> 1:u32 ^ dsa_T_acc_2_4541:u32)
dsa_R_SF_1_4543:bool = high:bool(dsa_R_ECX_32_1_4536:u32)
dsa_R_ZF_1_4544:bool = 0:u32 == dsa_R_ECX_32_1_4536:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x1, -1, u32, rd
  @context "R_EDX_32" = 0x1, -1, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_4545:bool = false
dsa_T_t_1_4546:u32 = dsa_R_EDX_32_1_4512:u32 & dsa_R_EDX_32_1_4512:u32
dsa_R_OF_1_4547:bool = false
dsa_R_CF_1_4548:bool = false
dsa_R_AF_1_4549:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_4552:bool =
  ~low:bool(let dsa_T_acc_1_4550:u32 :=
                                         dsa_T_t_1_4546:u32 >> 4:u32 ^
                                         dsa_T_t_1_4546:u32 in
            let dsa_T_acc_2_4551:u32 :=
                                         dsa_T_acc_1_4550:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4550:u32 in
            dsa_T_acc_2_4551:u32 >> 1:u32 ^ dsa_T_acc_2_4551:u32)
dsa_R_SF_1_4553:bool = high:bool(dsa_T_t_1_4546:u32)
dsa_R_ZF_1_4554:bool = 0:u32 == dsa_T_t_1_4546:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0xa, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x0, -1, u32, rd
  @context "mem32[0xdd01cc60]" = 0x30, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc60_1_4555:u8 = low:u8(0x30:u8)
dsa_R_EDI_32_1_4556:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_4557:u32 = pad:u32(pad:u8(dsa_mem_dd01cc60_1_4555:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x0, -1, u32, wr
  @context "R_EDX_32" = 0x1, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_4558:u32 = dsa_R_EDX_32_1_4512:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf0677, 0, u32, rd
  @context "R_EAX_32" = 0x30, -1, u32, rd
  @context "mem32[0xffaf0677]" = 0x8, 0, u8, wr
label pc_0xdcf03221
dsa_mem_ffaf0677_1_4559:u8 = low:u8(8:u8)
dsa_R_ESI_32_1_4560:u32 = 0xffaf0677:u32
dsa_mem_ffaf0677_1_4561:u8 = low:u8(low:u8(dsa_R_EAX_32_1_4557:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_4562:bool = false
dsa_R_EIP_1_4563:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_4554:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp119"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x30, -1, u32, wr
  @context "R_ECX_32" = 0x1, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_4564:u32 = dsa_R_ECX_32_1_4558:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf0677, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_4565:u32 = 0xffaf0677:u32
dsa_R_DF_1_4566:bool = false
dsa_T_t_1_4567:u32 = dsa_R_ESI_32_1_4565:u32
dsa_R_ESI_32_1_4568:u32 = dsa_R_ESI_32_1_4565:u32 - 1:u32
dsa_R_CF_1_4569:bool = dsa_T_t_1_4567:u32 < 1:u32
dsa_R_OF_1_4570:bool =
  high:bool((dsa_T_t_1_4567:u32 ^ 1:u32) &
            (dsa_T_t_1_4567:u32 ^ dsa_R_ESI_32_1_4568:u32))
dsa_R_AF_1_4571:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_4568:u32 ^ dsa_T_t_1_4567:u32 ^ 1:u32))
dsa_R_PF_3_4574:bool =
  ~low:bool(let dsa_T_acc_1_4572:u32 :=
                                         dsa_R_ESI_32_1_4568:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_4568:u32 in
            let dsa_T_acc_2_4573:u32 :=
                                         dsa_T_acc_1_4572:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4572:u32 in
            dsa_T_acc_2_4573:u32 >> 1:u32 ^ dsa_T_acc_2_4573:u32)
dsa_R_SF_1_4575:bool = high:bool(dsa_R_ESI_32_1_4568:u32)
dsa_R_ZF_1_4576:bool = 0:u32 == dsa_R_ESI_32_1_4568:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x1, -1, u32, rw
  @context "R_EDX_32" = 0x1, -1, u32, wr
  @context "R_EFLAGS" = 0x282, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_4577:bool = false
dsa_R_EBP_32_1_4578:u32 = 0xcccccccd:u32
dsa_R_AF_1_4579:bool = false
dsa_R_OF_1_4580:bool = false
dsa_R_SF_1_4581:bool = true
dsa_R_DF_1_4582:bool = false
dsa_R_CF_1_4583:bool = false
dsa_R_EFLAGS_1_4584:u32 = 0x282:u32
dsa_R_PF_1_4585:bool = false
dsa_T_t_1_4586:u64 =
  pad:u64(dsa_R_EAX_32_1_4564:u32) * pad:u64(dsa_R_EBP_32_1_4578:u32)
dsa_R_EAX_32_1_4587:u32 = extract:31:0:[dsa_T_t_1_4586:u64]
dsa_R_EDX_32_1_4588:u32 = extract:63:32:[dsa_T_t_1_4586:u64]
dsa_R_OF_1_4589:bool = extract:63:32:[dsa_T_t_1_4586:u64] <> 0:u32
dsa_R_CF_1_4590:bool = extract:63:32:[dsa_T_t_1_4586:u64] <> 0:u32
dsa_R_SF_1_4591:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_4592:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_4593:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_4594:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x0, -1, u32, rw
  @context "R_EFLAGS" = 0x282, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_4595:bool = false
dsa_T_origDEST_1_4596:u32 = dsa_R_EDX_32_1_4588:u32
dsa_T_origCOUNT_1_4597:u32 = 3:u32
dsa_R_EDX_32_1_4598:u32 = dsa_R_EDX_32_1_4588:u32 >> 3:u32
dsa_R_CF_1_4599:bool =
  if dsa_T_origCOUNT_1_4597:u32 == 0:u32 then dsa_R_CF_1_4590:bool else
  high:bool(dsa_T_origDEST_1_4596:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_4597:u32)
dsa_R_OF_1_4600:bool =
  if dsa_T_origCOUNT_1_4597:u32 == 0:u32 then dsa_R_OF_1_4589:bool else
  if dsa_T_origCOUNT_1_4597:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_4596:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_4601:bool =
  if dsa_T_origCOUNT_1_4597:u32 == 0:u32 then dsa_R_SF_1_4591:bool else
  high:bool(dsa_R_EDX_32_1_4598:u32)
dsa_R_ZF_1_4602:bool =
  if dsa_T_origCOUNT_1_4597:u32 == 0:u32 then dsa_R_ZF_1_4592:bool else
  0:u32 == dsa_R_EDX_32_1_4598:u32
dsa_R_PF_3_4605:bool =
  if dsa_T_origCOUNT_1_4597:u32 == 0:u32 then dsa_R_PF_1_4594:bool else
  ~low:bool(let dsa_T_acc_1_4603:u32 :=
                                         dsa_R_EDX_32_1_4598:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_4598:u32 in
            let dsa_T_acc_2_4604:u32 :=
                                         dsa_T_acc_1_4603:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4603:u32 in
            dsa_T_acc_2_4604:u32 >> 1:u32 ^ dsa_T_acc_2_4604:u32)
dsa_R_AF_1_4606:bool =
  if dsa_T_origCOUNT_1_4597:u32 == 0:u32 then dsa_R_AF_1_4593:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0xcccccccd, -1, u32, wr
  @context "R_EDX_32" = 0x0, -1, u32, rd
  @context "R_EDX_32" = 0x0, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_4607:u32 =
  dsa_R_EDX_32_1_4598:u32 + (dsa_R_EDX_32_1_4598:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x0, -1, u32, rw
  @context "R_EAX_32" = 0x0, -1, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_4608:bool = false
dsa_T_t1_1_4609:u32 = dsa_R_EAX_32_1_4607:u32
dsa_T_t2_1_4610:u32 = dsa_R_EAX_32_1_4607:u32
dsa_R_EAX_32_1_4611:u32 = dsa_R_EAX_32_1_4607:u32 + dsa_T_t2_1_4610:u32
dsa_R_CF_1_4612:bool = dsa_R_EAX_32_1_4611:u32 < dsa_T_t1_1_4609:u32
dsa_R_OF_1_4613:bool =
  high:bool((dsa_T_t1_1_4609:u32 ^ ~dsa_T_t2_1_4610:u32) &
            (dsa_T_t1_1_4609:u32 ^ dsa_R_EAX_32_1_4611:u32))
dsa_R_AF_1_4614:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_4611:u32 ^ dsa_T_t1_1_4609:u32 ^ dsa_T_t2_1_4610:u32))
dsa_R_PF_3_4617:bool =
  ~low:bool(let dsa_T_acc_1_4615:u32 :=
                                         dsa_R_EAX_32_1_4611:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_4611:u32 in
            let dsa_T_acc_2_4616:u32 :=
                                         dsa_T_acc_1_4615:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4615:u32 in
            dsa_T_acc_2_4616:u32 >> 1:u32 ^ dsa_T_acc_2_4616:u32)
dsa_R_SF_1_4618:bool = high:bool(dsa_R_EAX_32_1_4611:u32)
dsa_R_ZF_1_4619:bool = 0:u32 == dsa_R_EAX_32_1_4611:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x1, -1, u32, rw
  @context "R_EAX_32" = 0x0, -1, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_4620:bool = false
dsa_T_t_1_4621:u32 = dsa_R_ECX_32_1_4558:u32
dsa_R_ECX_32_1_4622:u32 = dsa_R_ECX_32_1_4558:u32 - dsa_R_EAX_32_1_4611:u32
dsa_R_CF_1_4623:bool = dsa_T_t_1_4621:u32 < dsa_R_EAX_32_1_4611:u32
dsa_R_OF_1_4624:bool =
  high:bool((dsa_T_t_1_4621:u32 ^ dsa_R_EAX_32_1_4611:u32) &
            (dsa_T_t_1_4621:u32 ^ dsa_R_ECX_32_1_4622:u32))
dsa_R_AF_1_4625:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_4622:u32 ^ dsa_T_t_1_4621:u32 ^ dsa_R_EAX_32_1_4611:u32))
dsa_R_PF_3_4628:bool =
  ~low:bool(let dsa_T_acc_1_4626:u32 :=
                                         dsa_R_ECX_32_1_4622:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_4622:u32 in
            let dsa_T_acc_2_4627:u32 :=
                                         dsa_T_acc_1_4626:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4626:u32 in
            dsa_T_acc_2_4627:u32 >> 1:u32 ^ dsa_T_acc_2_4627:u32)
dsa_R_SF_1_4629:bool = high:bool(dsa_R_ECX_32_1_4622:u32)
dsa_R_ZF_1_4630:bool = 0:u32 == dsa_R_ECX_32_1_4622:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x0, -1, u32, rd
  @context "R_EDX_32" = 0x0, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_4631:bool = false
dsa_T_t_1_4632:u32 = dsa_R_EDX_32_1_4598:u32 & dsa_R_EDX_32_1_4598:u32
dsa_R_OF_1_4633:bool = false
dsa_R_CF_1_4634:bool = false
dsa_R_AF_1_4635:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_4638:bool =
  ~low:bool(let dsa_T_acc_1_4636:u32 :=
                                         dsa_T_t_1_4632:u32 >> 4:u32 ^
                                         dsa_T_t_1_4632:u32 in
            let dsa_T_acc_2_4637:u32 :=
                                         dsa_T_acc_1_4636:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4636:u32 in
            dsa_T_acc_2_4637:u32 >> 1:u32 ^ dsa_T_acc_2_4637:u32)
dsa_R_SF_1_4639:bool = high:bool(dsa_T_t_1_4632:u32)
dsa_R_ZF_1_4640:bool = 0:u32 == dsa_T_t_1_4632:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x0, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x1, -1, u32, rd
  @context "mem32[0xdd01cc61]" = 0x31, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc61_1_4641:u8 = low:u8(0x31:u8)
dsa_R_EDI_32_1_4642:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_4643:u32 = pad:u32(pad:u8(dsa_mem_dd01cc61_1_4641:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x1, -1, u32, wr
  @context "R_EDX_32" = 0x0, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_4644:u32 = dsa_R_EDX_32_1_4598:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf0676, 0, u32, rd
  @context "R_EAX_32" = 0x31, -1, u32, rd
  @context "mem32[0xffaf0676]" = 0x4, 0, u8, wr
label pc_0xdcf03221
dsa_mem_ffaf0676_1_4645:u8 = low:u8(4:u8)
dsa_R_ESI_32_1_4646:u32 = 0xffaf0676:u32
dsa_mem_ffaf0676_1_4647:u8 = low:u8(low:u8(dsa_R_EAX_32_1_4643:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x246, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_4648:bool = false
dsa_R_EIP_1_4649:u32 = 0xdcf03223:u32
assert ~~dsa_R_ZF_1_4640:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp120"*/
label nocjmp120
addr 0xdcf03226 @asm "mov    eax,esi" @tid "0"
  @context "R_EAX_32" = 0x31, -1, u32, wr
  @context "R_ESI_32" = 0xffaf0676, 0, u32, rd
label pc_0xdcf03226
dsa_R_ESI_32_1_4650:u32 = 0xffaf0676:u32
dsa_R_EAX_32_1_4651:u32 = dsa_R_ESI_32_1_4650:u32
addr 0xdcf06929 @asm "cmp    DWORD PTR [ebp-0x484],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
  @context "mem32[0xffaf0214]" = 0xff, 0, u8, rd
  @context "mem32[0xffaf0215]" = 0xff, 0, u8, rd
  @context "mem32[0xffaf0216]" = 0xff, 0, u8, rd
  @context "mem32[0xffaf0217]" = 0xff, 0, u8, rd
label pc_0xdcf06929
dsa_mem_ffaf0216_1_4652:u8 = low:u8(-1:u8)
dsa_mem_ffaf0217_1_4653:u8 = low:u8(-1:u8)
dsa_mem_ffaf0215_1_4654:u8 = low:u8(-1:u8)
dsa_mem_ffaf0214_1_4655:u8 = low:u8(-1:u8)
dsa_R_EBP_32_1_4656:u32 = 0xffaf0698:u32
dsa_R_DF_1_4657:bool = false
dsa_T_t_1_4658:u32 =
  (pad:u32(dsa_mem_ffaf0217_1_4653:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf0216_1_4652:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf0215_1_4654:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf0214_1_4655:u8)))) - 0:u32
dsa_R_CF_1_4659:bool =
  (pad:u32(dsa_mem_ffaf0217_1_4653:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf0216_1_4652:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf0215_1_4654:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf0214_1_4655:u8)))) < 0:u32
dsa_R_OF_1_4660:bool =
  high:bool(((pad:u32(dsa_mem_ffaf0217_1_4653:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf0216_1_4652:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf0215_1_4654:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf0214_1_4655:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf0217_1_4653:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf0216_1_4652:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf0215_1_4654:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf0214_1_4655:u8)))) ^ dsa_T_t_1_4658:u32))
dsa_R_AF_1_4661:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_4658:u32 ^
   (pad:u32(dsa_mem_ffaf0217_1_4653:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf0216_1_4652:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf0215_1_4654:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf0214_1_4655:u8)))) ^ 0:u32))
dsa_R_PF_3_4664:bool =
  ~low:bool(let dsa_T_acc_1_4662:u32 :=
                                         dsa_T_t_1_4658:u32 >> 4:u32 ^
                                         dsa_T_t_1_4658:u32 in
            let dsa_T_acc_2_4663:u32 :=
                                         dsa_T_acc_1_4662:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4662:u32 in
            dsa_T_acc_2_4663:u32 >> 1:u32 ^ dsa_T_acc_2_4663:u32)
dsa_R_SF_1_4665:bool = high:bool(dsa_T_t_1_4658:u32)
dsa_R_ZF_1_4666:bool = 0:u32 == dsa_T_t_1_4658:u32
addr 0xdcf03ec7 @asm "cmp    DWORD PTR [ebp-0x4b8],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x293, 0, u32, wr
  @context "mem32[0xffaf01e0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e3]" = 0x41, -1, u8, rd
label pc_0xdcf03ec7
dsa_R_ZF_1_4667:bool = false
dsa_R_EBP_32_1_4668:u32 = 0xffaf0698:u32
dsa_R_AF_1_4669:bool = true
dsa_R_OF_1_4670:bool = false
dsa_R_SF_1_4671:bool = true
dsa_R_DF_1_4672:bool = false
dsa_R_CF_1_4673:bool = true
dsa_R_EFLAGS_1_4674:u32 = 0x293:u32
dsa_R_PF_1_4675:bool = false
dsa_T_t_1_4676:u32 =
  (pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) - 0:u32
dsa_R_CF_1_4677:bool =
  (pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) < 0:u32
dsa_R_OF_1_4678:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) ^ dsa_T_t_1_4676:u32))
dsa_R_AF_1_4679:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_4676:u32 ^
   (pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) ^ 0:u32))
dsa_R_PF_3_4682:bool =
  ~low:bool(let dsa_T_acc_1_4680:u32 :=
                                         dsa_T_t_1_4676:u32 >> 4:u32 ^
                                         dsa_T_t_1_4676:u32 in
            let dsa_T_acc_2_4681:u32 :=
                                         dsa_T_acc_1_4680:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4680:u32 in
            dsa_T_acc_2_4681:u32 >> 1:u32 ^ dsa_T_acc_2_4681:u32)
dsa_R_SF_1_4683:bool = high:bool(dsa_T_t_1_4676:u32)
dsa_R_ZF_1_4684:bool = 0:u32 == dsa_T_t_1_4676:u32
addr 0xdcf03ece @asm "je     0x00000000dcf03ef5" @tid "0"
  @context "R_EIP" = 0xdcf03ece, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcf03ece
dsa_R_DF_1_4685:bool = false
dsa_R_EIP_1_4686:u32 = 0xdcf03ece:u32
assert ~dsa_R_ZF_1_4684:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf03ef5:u32, "nocjmp121"*/
label nocjmp121
addr 0xdcf03ed0 @asm "cmp    DWORD PTR [ebp-0x4b0],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
  @context "mem32[0xffaf01e8]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e9]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01ea]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01eb]" = 0x0, 0, u8, rd
label pc_0xdcf03ed0
dsa_mem_ffaf01eb_1_4687:u8 = low:u8(0:u8)
dsa_mem_ffaf01e8_1_4688:u8 = low:u8(0:u8)
dsa_mem_ffaf01e9_1_4689:u8 = low:u8(0:u8)
dsa_mem_ffaf01ea_1_4690:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_4691:u32 = 0xffaf0698:u32
dsa_R_DF_1_4692:bool = false
dsa_T_t_1_4693:u32 =
  (pad:u32(dsa_mem_ffaf01eb_1_4687:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01ea_1_4690:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e9_1_4689:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e8_1_4688:u8)))) - 0:u32
dsa_R_CF_1_4694:bool =
  (pad:u32(dsa_mem_ffaf01eb_1_4687:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01ea_1_4690:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e9_1_4689:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e8_1_4688:u8)))) < 0:u32
dsa_R_OF_1_4695:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01eb_1_4687:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01ea_1_4690:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e9_1_4689:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e8_1_4688:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01eb_1_4687:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01ea_1_4690:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e9_1_4689:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e8_1_4688:u8)))) ^ dsa_T_t_1_4693:u32))
dsa_R_AF_1_4696:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_4693:u32 ^
   (pad:u32(dsa_mem_ffaf01eb_1_4687:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01ea_1_4690:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e9_1_4689:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e8_1_4688:u8)))) ^ 0:u32))
dsa_R_PF_3_4699:bool =
  ~low:bool(let dsa_T_acc_1_4697:u32 :=
                                         dsa_T_t_1_4693:u32 >> 4:u32 ^
                                         dsa_T_t_1_4693:u32 in
            let dsa_T_acc_2_4698:u32 :=
                                         dsa_T_acc_1_4697:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4697:u32 in
            dsa_T_acc_2_4698:u32 >> 1:u32 ^ dsa_T_acc_2_4698:u32)
dsa_R_SF_1_4700:bool = high:bool(dsa_T_t_1_4693:u32)
dsa_R_ZF_1_4701:bool = 0:u32 == dsa_T_t_1_4693:u32
addr 0xdcf03efb @asm "mov    edx,DWORD PTR [ebp-0x49c]" @tid "0"
  @context "R_EDX_32" = 0x0, -1, u32, wr
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "mem32[0xffaf01fc]" = 0x1, 0, u8, rd
  @context "mem32[0xffaf01fd]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01fe]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01ff]" = 0x0, 0, u8, rd
label pc_0xdcf03efb
dsa_mem_ffaf01fe_1_4702:u8 = low:u8(0:u8)
dsa_mem_ffaf01fc_1_4703:u8 = low:u8(1:u8)
dsa_mem_ffaf01fd_1_4704:u8 = low:u8(0:u8)
dsa_mem_ffaf01ff_1_4705:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_4706:u32 = 0xffaf0698:u32
dsa_R_EDX_32_1_4707:u32 =
  pad:u32(dsa_mem_ffaf01ff_1_4705:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01fe_1_4702:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01fd_1_4704:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01fc_1_4703:u8)))
addr 0xdcf03f34 @asm "cmp    DWORD PTR [ebp-0x4b8],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
  @context "mem32[0xffaf01e0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e3]" = 0x41, -1, u8, rd
label pc_0xdcf03f34
dsa_R_ZF_1_4708:bool = false
dsa_R_EBP_32_1_4709:u32 = 0xffaf0698:u32
dsa_R_AF_1_4710:bool = false
dsa_R_OF_1_4711:bool = false
dsa_R_SF_1_4712:bool = true
dsa_R_DF_1_4713:bool = false
dsa_R_CF_1_4714:bool = false
dsa_R_EFLAGS_1_4715:u32 = 0x286:u32
dsa_R_PF_1_4716:bool = true
dsa_T_t_1_4717:u32 =
  (pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) - 0:u32
dsa_R_CF_1_4718:bool =
  (pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) < 0:u32
dsa_R_OF_1_4719:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) ^ dsa_T_t_1_4717:u32))
dsa_R_AF_1_4720:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_4717:u32 ^
   (pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) ^ 0:u32))
dsa_R_PF_3_4723:bool =
  ~low:bool(let dsa_T_acc_1_4721:u32 :=
                                         dsa_T_t_1_4717:u32 >> 4:u32 ^
                                         dsa_T_t_1_4717:u32 in
            let dsa_T_acc_2_4722:u32 :=
                                         dsa_T_acc_1_4721:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4721:u32 in
            dsa_T_acc_2_4722:u32 >> 1:u32 ^ dsa_T_acc_2_4722:u32)
dsa_R_SF_1_4724:bool = high:bool(dsa_T_t_1_4717:u32)
dsa_R_ZF_1_4725:bool = 0:u32 == dsa_T_t_1_4717:u32
addr 0xdcf03f3b @asm "je     0x00000000dcf03f58" @tid "0"
  @context "R_EIP" = 0xdcf03f3b, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcf03f3b
dsa_R_DF_1_4726:bool = false
dsa_R_EIP_1_4727:u32 = 0xdcf03f3b:u32
assert ~dsa_R_ZF_1_4725:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf03f58:u32, "nocjmp122"*/
label nocjmp122
addr 0xdcf03f3d @asm "cmp    DWORD PTR [ebp-0x4b0],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
  @context "mem32[0xffaf01e8]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e9]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01ea]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01eb]" = 0x0, 0, u8, rd
label pc_0xdcf03f3d
dsa_mem_ffaf01eb_1_4728:u8 = low:u8(0:u8)
dsa_mem_ffaf01e8_1_4729:u8 = low:u8(0:u8)
dsa_mem_ffaf01e9_1_4730:u8 = low:u8(0:u8)
dsa_mem_ffaf01ea_1_4731:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_4732:u32 = 0xffaf0698:u32
dsa_R_DF_1_4733:bool = false
dsa_T_t_1_4734:u32 =
  (pad:u32(dsa_mem_ffaf01eb_1_4728:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01ea_1_4731:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e9_1_4730:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e8_1_4729:u8)))) - 0:u32
dsa_R_CF_1_4735:bool =
  (pad:u32(dsa_mem_ffaf01eb_1_4728:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01ea_1_4731:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e9_1_4730:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e8_1_4729:u8)))) < 0:u32
dsa_R_OF_1_4736:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01eb_1_4728:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01ea_1_4731:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e9_1_4730:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e8_1_4729:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01eb_1_4728:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01ea_1_4731:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e9_1_4730:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e8_1_4729:u8)))) ^ dsa_T_t_1_4734:u32))
dsa_R_AF_1_4737:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_4734:u32 ^
   (pad:u32(dsa_mem_ffaf01eb_1_4728:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01ea_1_4731:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e9_1_4730:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e8_1_4729:u8)))) ^ 0:u32))
dsa_R_PF_3_4740:bool =
  ~low:bool(let dsa_T_acc_1_4738:u32 :=
                                         dsa_T_t_1_4734:u32 >> 4:u32 ^
                                         dsa_T_t_1_4734:u32 in
            let dsa_T_acc_2_4739:u32 :=
                                         dsa_T_acc_1_4738:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4738:u32 in
            dsa_T_acc_2_4739:u32 >> 1:u32 ^ dsa_T_acc_2_4739:u32)
dsa_R_SF_1_4741:bool = high:bool(dsa_T_t_1_4734:u32)
dsa_R_ZF_1_4742:bool = 0:u32 == dsa_T_t_1_4734:u32
addr 0xdcf03f5e @asm "or     eax,DWORD PTR [ebp-0x4bc]" @tid "0"
  @context "R_EAX_32" = 0x0, 0, u32, rw
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, 0, u32, wr
  @context "mem32[0xffaf01dc]" = 0x0, -1, u8, rd
  @context "mem32[0xffaf01dd]" = 0x0, -1, u8, rd
  @context "mem32[0xffaf01de]" = 0x0, -1, u8, rd
  @context "mem32[0xffaf01df]" = 0x0, -1, u8, rd
label pc_0xdcf03f5e
dsa_R_ZF_1_4743:bool = true
dsa_R_EBP_32_1_4744:u32 = 0xffaf0698:u32
dsa_R_AF_1_4745:bool = false
dsa_R_OF_1_4746:bool = false
dsa_R_SF_1_4747:bool = false
dsa_R_DF_1_4748:bool = false
dsa_R_EAX_32_1_4749:u32 = 0:u32
dsa_R_CF_1_4750:bool = false
dsa_R_EFLAGS_1_4751:u32 = 0x246:u32
dsa_R_PF_1_4752:bool = true
dsa_R_EAX_32_1_4753:u32 =
  dsa_R_EAX_32_1_4749:u32 |
  (pad:u32(dsa_mem_ffaf01df_1_3741:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01de_1_3740:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01dd_1_3739:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01dc_1_3738:u8))))
dsa_R_OF_1_4754:bool = false
dsa_R_CF_1_4755:bool = false
dsa_R_AF_1_4756:bool = unknown "AF is undefined after or":bool
dsa_R_PF_3_4759:bool =
  ~low:bool(let dsa_T_acc_1_4757:u32 :=
                                         dsa_R_EAX_32_1_4753:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_4753:u32 in
            let dsa_T_acc_2_4758:u32 :=
                                         dsa_T_acc_1_4757:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4757:u32 in
            dsa_T_acc_2_4758:u32 >> 1:u32 ^ dsa_T_acc_2_4758:u32)
dsa_R_SF_1_4760:bool = high:bool(dsa_R_EAX_32_1_4753:u32)
dsa_R_ZF_1_4761:bool = 0:u32 == dsa_R_EAX_32_1_4753:u32
addr 0xdcf03f64 @asm "or     eax,DWORD PTR [ebp-0x4b4]" @tid "0"
  @context "R_EAX_32" = 0x0, -1, u32, rw
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
  @context "mem32[0xffaf01e4]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e5]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e6]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e7]" = 0x0, 0, u8, rd
label pc_0xdcf03f64
dsa_mem_ffaf01e4_1_4762:u8 = low:u8(0:u8)
dsa_mem_ffaf01e5_1_4763:u8 = low:u8(0:u8)
dsa_mem_ffaf01e7_1_4764:u8 = low:u8(0:u8)
dsa_mem_ffaf01e6_1_4765:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_4766:u32 = 0xffaf0698:u32
dsa_R_DF_1_4767:bool = false
dsa_R_EAX_32_1_4768:u32 =
  dsa_R_EAX_32_1_4753:u32 |
  (pad:u32(dsa_mem_ffaf01e7_1_4764:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e6_1_4765:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e5_1_4763:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e4_1_4762:u8))))
dsa_R_OF_1_4769:bool = false
dsa_R_CF_1_4770:bool = false
dsa_R_AF_1_4771:bool = unknown "AF is undefined after or":bool
dsa_R_PF_3_4774:bool =
  ~low:bool(let dsa_T_acc_1_4772:u32 :=
                                         dsa_R_EAX_32_1_4768:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_4768:u32 in
            let dsa_T_acc_2_4773:u32 :=
                                         dsa_T_acc_1_4772:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4772:u32 in
            dsa_T_acc_2_4773:u32 >> 1:u32 ^ dsa_T_acc_2_4773:u32)
dsa_R_SF_1_4775:bool = high:bool(dsa_R_EAX_32_1_4768:u32)
dsa_R_ZF_1_4776:bool = 0:u32 == dsa_R_EAX_32_1_4768:u32
addr 0xdcf03f6a @asm "cmp    eax,0x1" @tid "0"
  @context "R_EAX_32" = 0x0, -1, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
label pc_0xdcf03f6a
dsa_R_DF_1_4777:bool = false
dsa_T_t_1_4778:u32 = dsa_R_EAX_32_1_4768:u32 - 1:u32
dsa_R_CF_1_4779:bool = dsa_R_EAX_32_1_4768:u32 < 1:u32
dsa_R_OF_1_4780:bool =
  high:bool((dsa_R_EAX_32_1_4768:u32 ^ 1:u32) &
            (dsa_R_EAX_32_1_4768:u32 ^ dsa_T_t_1_4778:u32))
dsa_R_AF_1_4781:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_T_t_1_4778:u32 ^ dsa_R_EAX_32_1_4768:u32 ^ 1:u32))
dsa_R_PF_3_4784:bool =
  ~low:bool(let dsa_T_acc_1_4782:u32 :=
                                         dsa_T_t_1_4778:u32 >> 4:u32 ^
                                         dsa_T_t_1_4778:u32 in
            let dsa_T_acc_2_4783:u32 :=
                                         dsa_T_acc_1_4782:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4782:u32 in
            dsa_T_acc_2_4783:u32 >> 1:u32 ^ dsa_T_acc_2_4783:u32)
dsa_R_SF_1_4785:bool = high:bool(dsa_T_t_1_4778:u32)
dsa_R_ZF_1_4786:bool = 0:u32 == dsa_T_t_1_4778:u32
addr 0xdcf03f6d @asm "adc    edx,0xffffffff" @tid "0"
  @context "R_EDX_32" = 0xfffffff6, 0, u32, rw
  @context "R_EFLAGS" = 0x297, -1, u32, rw
label pc_0xdcf03f6d
dsa_R_DF_1_4787:bool = false
dsa_R_EDX_32_1_4788:u32 = 0xfffffff6:u32
dsa_T_orig1_1_4789:u32 = dsa_R_EDX_32_1_4788:u32
dsa_T_orig2_1_4790:u32 = -1:u32
dsa_R_EDX_32_1_4791:u32 =
  dsa_T_orig1_1_4789:u32 + dsa_T_orig2_1_4790:u32 +
  pad:u32(dsa_R_CF_1_4779:bool)
dsa_R_CF_1_4792:bool =
  extract:32:32:[pad:u33(dsa_T_orig1_1_4789:u32) +
                 pad:u33(dsa_T_orig2_1_4790:u32) +
                 pad:u33(dsa_R_CF_1_4779:bool)]
dsa_R_OF_1_4793:bool =
  high:bool((dsa_T_orig1_1_4789:u32 ^ ~dsa_T_orig2_1_4790:u32) &
            (dsa_T_orig1_1_4789:u32 ^ dsa_R_EDX_32_1_4791:u32))
dsa_R_AF_1_4794:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EDX_32_1_4791:u32 ^ dsa_T_orig1_1_4789:u32 ^ dsa_T_orig2_1_4790:u32))
dsa_R_PF_3_4797:bool =
  ~low:bool(let dsa_T_acc_1_4795:u32 :=
                                         dsa_R_EDX_32_1_4791:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_4791:u32 in
            let dsa_T_acc_2_4796:u32 :=
                                         dsa_T_acc_1_4795:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4795:u32 in
            dsa_T_acc_2_4796:u32 >> 1:u32 ^ dsa_T_acc_2_4796:u32)
dsa_R_SF_1_4798:bool = high:bool(dsa_R_EDX_32_1_4791:u32)
dsa_R_ZF_1_4799:bool = 0:u32 == dsa_R_EDX_32_1_4791:u32
addr 0xdcf03f7d @asm "cmp    DWORD PTR [ebp-0x4bc],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, 0, u32, wr
  @context "mem32[0xffaf01dc]" = 0x0, -1, u8, rd
  @context "mem32[0xffaf01dd]" = 0x0, -1, u8, rd
  @context "mem32[0xffaf01de]" = 0x0, -1, u8, rd
  @context "mem32[0xffaf01df]" = 0x0, -1, u8, rd
label pc_0xdcf03f7d
dsa_R_ZF_1_4800:bool = true
dsa_R_EBP_32_1_4801:u32 = 0xffaf0698:u32
dsa_R_AF_1_4802:bool = false
dsa_R_OF_1_4803:bool = false
dsa_R_SF_1_4804:bool = false
dsa_R_DF_1_4805:bool = false
dsa_R_CF_1_4806:bool = false
dsa_R_EFLAGS_1_4807:u32 = 0x246:u32
dsa_R_PF_1_4808:bool = true
dsa_T_t_1_4809:u32 =
  (pad:u32(dsa_mem_ffaf01df_1_3741:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01de_1_3740:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01dd_1_3739:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01dc_1_3738:u8)))) - 0:u32
dsa_R_CF_1_4810:bool =
  (pad:u32(dsa_mem_ffaf01df_1_3741:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01de_1_3740:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01dd_1_3739:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01dc_1_3738:u8)))) < 0:u32
dsa_R_OF_1_4811:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01df_1_3741:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01de_1_3740:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01dd_1_3739:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01dc_1_3738:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01df_1_3741:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01de_1_3740:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01dd_1_3739:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01dc_1_3738:u8)))) ^ dsa_T_t_1_4809:u32))
dsa_R_AF_1_4812:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_4809:u32 ^
   (pad:u32(dsa_mem_ffaf01df_1_3741:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01de_1_3740:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01dd_1_3739:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01dc_1_3738:u8)))) ^ 0:u32))
dsa_R_PF_3_4815:bool =
  ~low:bool(let dsa_T_acc_1_4813:u32 :=
                                         dsa_T_t_1_4809:u32 >> 4:u32 ^
                                         dsa_T_t_1_4809:u32 in
            let dsa_T_acc_2_4814:u32 :=
                                         dsa_T_acc_1_4813:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4813:u32 in
            dsa_T_acc_2_4814:u32 >> 1:u32 ^ dsa_T_acc_2_4814:u32)
dsa_R_SF_1_4816:bool = high:bool(dsa_T_t_1_4809:u32)
dsa_R_ZF_1_4817:bool = 0:u32 == dsa_T_t_1_4809:u32
addr 0xdcf03f84 @asm "je     0x00000000dcf06677" @tid "0"
  @context "R_EIP" = 0xdcf03f84, 0, u32, rw
  @context "R_EFLAGS" = 0x246, -1, u32, rd
label pc_0xdcf03f84
dsa_R_DF_1_4818:bool = false
dsa_R_EIP_1_4819:u32 = 0xdcf03f84:u32
assert dsa_R_ZF_1_4817:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf06677:u32, "nocjmp123"*/
addr 0xdcf06677 @asm "cmp    DWORD PTR [ebp-0x4b4],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
  @context "mem32[0xffaf01e4]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e5]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e6]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e7]" = 0x0, 0, u8, rd
label pc_0xdcf06677
dsa_mem_ffaf01e4_1_4820:u8 = low:u8(0:u8)
dsa_mem_ffaf01e5_1_4821:u8 = low:u8(0:u8)
dsa_mem_ffaf01e7_1_4822:u8 = low:u8(0:u8)
dsa_mem_ffaf01e6_1_4823:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_4824:u32 = 0xffaf0698:u32
dsa_R_DF_1_4825:bool = false
dsa_T_t_1_4826:u32 =
  (pad:u32(dsa_mem_ffaf01e7_1_4822:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e6_1_4823:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e5_1_4821:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e4_1_4820:u8)))) - 0:u32
dsa_R_CF_1_4827:bool =
  (pad:u32(dsa_mem_ffaf01e7_1_4822:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e6_1_4823:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e5_1_4821:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e4_1_4820:u8)))) < 0:u32
dsa_R_OF_1_4828:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01e7_1_4822:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e6_1_4823:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e5_1_4821:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e4_1_4820:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01e7_1_4822:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e6_1_4823:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e5_1_4821:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e4_1_4820:u8)))) ^ dsa_T_t_1_4826:u32))
dsa_R_AF_1_4829:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_4826:u32 ^
   (pad:u32(dsa_mem_ffaf01e7_1_4822:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01e6_1_4823:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e5_1_4821:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e4_1_4820:u8)))) ^ 0:u32))
dsa_R_PF_3_4832:bool =
  ~low:bool(let dsa_T_acc_1_4830:u32 :=
                                         dsa_T_t_1_4826:u32 >> 4:u32 ^
                                         dsa_T_t_1_4826:u32 in
            let dsa_T_acc_2_4831:u32 :=
                                         dsa_T_acc_1_4830:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4830:u32 in
            dsa_T_acc_2_4831:u32 >> 1:u32 ^ dsa_T_acc_2_4831:u32)
dsa_R_SF_1_4833:bool = high:bool(dsa_T_t_1_4826:u32)
dsa_R_ZF_1_4834:bool = 0:u32 == dsa_T_t_1_4826:u32
addr 0xdcf03fb6 @asm "cmp    DWORD PTR [ebp-0x4b8],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, 0, u32, wr
  @context "mem32[0xffaf01e0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e3]" = 0x41, -1, u8, rd
label pc_0xdcf03fb6
dsa_R_ZF_1_4835:bool = true
dsa_R_EBP_32_1_4836:u32 = 0xffaf0698:u32
dsa_R_AF_1_4837:bool = false
dsa_R_OF_1_4838:bool = false
dsa_R_SF_1_4839:bool = false
dsa_R_DF_1_4840:bool = false
dsa_R_CF_1_4841:bool = false
dsa_R_EFLAGS_1_4842:u32 = 0x246:u32
dsa_R_PF_1_4843:bool = true
dsa_T_t_1_4844:u32 =
  (pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) - 0:u32
dsa_R_CF_1_4845:bool =
  (pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) < 0:u32
dsa_R_OF_1_4846:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) ^ dsa_T_t_1_4844:u32))
dsa_R_AF_1_4847:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_4844:u32 ^
   (pad:u32(dsa_mem_ffaf01e3_1_3750:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01e2_1_3749:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e1_1_3748:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e0_1_3747:u8)))) ^ 0:u32))
dsa_R_PF_3_4850:bool =
  ~low:bool(let dsa_T_acc_1_4848:u32 :=
                                         dsa_T_t_1_4844:u32 >> 4:u32 ^
                                         dsa_T_t_1_4844:u32 in
            let dsa_T_acc_2_4849:u32 :=
                                         dsa_T_acc_1_4848:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4848:u32 in
            dsa_T_acc_2_4849:u32 >> 1:u32 ^ dsa_T_acc_2_4849:u32)
dsa_R_SF_1_4851:bool = high:bool(dsa_T_t_1_4844:u32)
dsa_R_ZF_1_4852:bool = 0:u32 == dsa_T_t_1_4844:u32
addr 0xdcf03fbd @asm "je     0x00000000dcf04028" @tid "0"
  @context "R_EIP" = 0xdcf03fbd, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcf03fbd
dsa_R_DF_1_4853:bool = false
dsa_R_EIP_1_4854:u32 = 0xdcf03fbd:u32
assert ~dsa_R_ZF_1_4852:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf04028:u32, "nocjmp124"*/
label nocjmp124
addr 0xdcf03fbf @asm "cmp    DWORD PTR [ebp-0x4b0],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
  @context "mem32[0xffaf01e8]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e9]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01ea]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01eb]" = 0x0, 0, u8, rd
label pc_0xdcf03fbf
dsa_mem_ffaf01eb_1_4855:u8 = low:u8(0:u8)
dsa_mem_ffaf01e8_1_4856:u8 = low:u8(0:u8)
dsa_mem_ffaf01e9_1_4857:u8 = low:u8(0:u8)
dsa_mem_ffaf01ea_1_4858:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_4859:u32 = 0xffaf0698:u32
dsa_R_DF_1_4860:bool = false
dsa_T_t_1_4861:u32 =
  (pad:u32(dsa_mem_ffaf01eb_1_4855:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01ea_1_4858:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e9_1_4857:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e8_1_4856:u8)))) - 0:u32
dsa_R_CF_1_4862:bool =
  (pad:u32(dsa_mem_ffaf01eb_1_4855:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01ea_1_4858:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e9_1_4857:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e8_1_4856:u8)))) < 0:u32
dsa_R_OF_1_4863:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01eb_1_4855:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01ea_1_4858:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e9_1_4857:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e8_1_4856:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01eb_1_4855:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01ea_1_4858:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e9_1_4857:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e8_1_4856:u8)))) ^ dsa_T_t_1_4861:u32))
dsa_R_AF_1_4864:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_4861:u32 ^
   (pad:u32(dsa_mem_ffaf01eb_1_4855:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01ea_1_4858:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e9_1_4857:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e8_1_4856:u8)))) ^ 0:u32))
dsa_R_PF_3_4867:bool =
  ~low:bool(let dsa_T_acc_1_4865:u32 :=
                                         dsa_T_t_1_4861:u32 >> 4:u32 ^
                                         dsa_T_t_1_4861:u32 in
            let dsa_T_acc_2_4866:u32 :=
                                         dsa_T_acc_1_4865:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4865:u32 in
            dsa_T_acc_2_4866:u32 >> 1:u32 ^ dsa_T_acc_2_4866:u32)
dsa_R_SF_1_4868:bool = high:bool(dsa_T_t_1_4861:u32)
dsa_R_ZF_1_4869:bool = 0:u32 == dsa_T_t_1_4861:u32
addr 0xdcf0408a @asm "movsx  eax,BYTE PTR [esi+0x46]" @tid "0"
  @context "R_EAX_32" = 0x0, -1, u32, wr
  @context "R_ESI_32" = 0xdd06dac0, 0, u32, rd
  @context "mem32[0xdd06db06]" = 0x0, 0, u8, rd
label pc_0xdcf0408a
dsa_mem_dd06db06_1_4870:u8 = low:u8(0:u8)
dsa_R_ESI_32_1_4871:u32 = 0xdd06dac0:u32
dsa_R_EAX_32_1_4872:u32 = extend:u32(pad:u8(dsa_mem_dd06db06_1_4870:u8))
addr 0xdcf0408e @asm "mov    ecx,DWORD PTR [ebp-0x478]" @tid "0"
  @context "R_ECX_32" = 0x0, -1, u32, wr
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "mem32[0xffaf0220]" = 0x76, 0, u8, rd
  @context "mem32[0xffaf0221]" = 0x6, 0, u8, rd
  @context "mem32[0xffaf0222]" = 0xaf, 0, u8, rd
  @context "mem32[0xffaf0223]" = 0xff, 0, u8, rd
label pc_0xdcf0408e
dsa_mem_ffaf0220_1_4873:u8 = low:u8(0x76:u8)
dsa_mem_ffaf0223_1_4874:u8 = low:u8(-1:u8)
dsa_mem_ffaf0222_1_4875:u8 = low:u8(0xaf:u8)
dsa_mem_ffaf0221_1_4876:u8 = low:u8(6:u8)
dsa_R_EBP_32_1_4877:u32 = 0xffaf0698:u32
dsa_R_ECX_32_1_4878:u32 =
  pad:u32(dsa_mem_ffaf0223_1_4874:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf0222_1_4875:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf0221_1_4876:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf0220_1_4873:u8)))
addr 0xdcf040a5 @asm "mov    DWORD PTR [esp],esi" @tid "0"
  @context "R_ESP_32" = 0xffaf0180, 0, u32, rd
  @context "R_ESI_32" = 0xdd06dac0, 0, u32, rd
  @context "mem32[0xffaf0180]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf0181]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf0182]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf0183]" = 0x41, -1, u8, wr
label pc_0xdcf040a5
dsa_R_ESI_32_1_4879:u32 = 0xdd06dac0:u32
dsa_R_ESP_32_1_4880:u32 = 0xffaf0180:u32
dsa_mem_ffaf0180_1_4881:u8 = low:u8(dsa_R_ESI_32_1_4879:u32)
dsa_mem_ffaf0181_1_4882:u8 = low:u8(dsa_R_ESI_32_1_4879:u32 >> 8:u32)
dsa_mem_ffaf0182_1_4883:u8 = low:u8(dsa_R_ESI_32_1_4879:u32 >> 0x10:u32)
dsa_mem_ffaf0183_1_4884:u8 = low:u8(dsa_R_ESI_32_1_4879:u32 >> 0x18:u32)
addr 0xdcf2f378 @asm "cmp    BYTE PTR [ebp-0x1],0xa" @tid "0"
  @context "R_EBP_32" = 0xffaf0680, 0, u32, rd
  @context "R_EFLAGS" = 0x287, 0, u32, wr
  @context "mem32[0xffaf067f]" = 0x35, -1, u8, rd
label pc_0xdcf2f378
dsa_R_ZF_1_4885:bool = false
dsa_R_EBP_32_1_4886:u32 = 0xffaf0680:u32
dsa_R_AF_1_4887:bool = false
dsa_R_OF_1_4888:bool = false
dsa_R_SF_1_4889:bool = true
dsa_R_DF_1_4890:bool = false
dsa_R_CF_1_4891:bool = true
dsa_R_EFLAGS_1_4892:u32 = 0x287:u32
dsa_R_PF_1_4893:bool = true
dsa_T_t_1_4894:u8 = pad:u8(dsa_mem_ffaf067f_1_3873:u8) - 0xa:u8
dsa_R_CF_1_4895:bool = pad:u8(dsa_mem_ffaf067f_1_3873:u8) < 0xa:u8
dsa_R_OF_1_4896:bool =
  high:bool((pad:u8(dsa_mem_ffaf067f_1_3873:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf067f_1_3873:u8) ^ dsa_T_t_1_4894:u8))
dsa_R_AF_1_4897:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_4894:u8 ^ pad:u8(dsa_mem_ffaf067f_1_3873:u8) ^ 0xa:u8))
dsa_R_PF_3_4900:bool =
  ~low:bool(let dsa_T_acc_1_4898:u8 :=
                                        dsa_T_t_1_4894:u8 >> 4:u8 ^
                                        dsa_T_t_1_4894:u8 in
            let dsa_T_acc_2_4899:u8 :=
                                        dsa_T_acc_1_4898:u8 >> 2:u8 ^
                                        dsa_T_acc_1_4898:u8 in
            dsa_T_acc_2_4899:u8 >> 1:u8 ^ dsa_T_acc_2_4899:u8)
dsa_R_SF_1_4901:bool = high:bool(dsa_T_t_1_4894:u8)
dsa_R_ZF_1_4902:bool = 0:u8 == dsa_T_t_1_4894:u8
addr 0xdcf2f37f @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f37f, 0, u32, rw
  @context "R_EFLAGS" = 0x216, -1, u32, rd
label pc_0xdcf2f37f
dsa_R_DF_1_4903:bool = false
dsa_R_EIP_1_4904:u32 = 0xdcf2f37f:u32
assert ~dsa_R_ZF_1_4902:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp125"*/
label nocjmp125
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf067f, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_4905:u32 = 0xffaf0676:u32
dsa_R_DF_1_4906:bool = false
dsa_R_EDX_32_1_4907:u32 = 0xffaf067f:u32
dsa_T_t_1_4908:u32 = dsa_R_EDX_32_1_4907:u32 - dsa_R_EBP_32_1_4905:u32
dsa_R_CF_1_4909:bool = dsa_R_EDX_32_1_4907:u32 < dsa_R_EBP_32_1_4905:u32
dsa_R_OF_1_4910:bool =
  high:bool((dsa_R_EDX_32_1_4907:u32 ^ dsa_R_EBP_32_1_4905:u32) &
            (dsa_R_EDX_32_1_4907:u32 ^ dsa_T_t_1_4908:u32))
dsa_R_AF_1_4911:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_4908:u32 ^ dsa_R_EDX_32_1_4907:u32 ^ dsa_R_EBP_32_1_4905:u32))
dsa_R_PF_3_4914:bool =
  ~low:bool(let dsa_T_acc_1_4912:u32 :=
                                         dsa_T_t_1_4908:u32 >> 4:u32 ^
                                         dsa_T_t_1_4908:u32 in
            let dsa_T_acc_2_4913:u32 :=
                                         dsa_T_acc_1_4912:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4912:u32 in
            dsa_T_acc_2_4913:u32 >> 1:u32 ^ dsa_T_acc_2_4913:u32)
dsa_R_SF_1_4915:bool = high:bool(dsa_T_t_1_4908:u32)
dsa_R_ZF_1_4916:bool = 0:u32 == dsa_T_t_1_4908:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf067e, 0, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
  @context "mem32[0xffaf067e]" = 0x38, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_4917:bool = false
dsa_R_AF_1_4918:bool = false
dsa_R_OF_1_4919:bool = false
dsa_R_SF_1_4920:bool = true
dsa_R_DF_1_4921:bool = false
dsa_R_EDX_32_1_4922:u32 = 0xffaf067e:u32
dsa_R_CF_1_4923:bool = false
dsa_R_EFLAGS_1_4924:u32 = 0x286:u32
dsa_R_PF_1_4925:bool = true
dsa_T_t_1_4926:u8 = pad:u8(dsa_mem_ffaf067e_1_3959:u8) - 0xa:u8
dsa_R_CF_1_4927:bool = pad:u8(dsa_mem_ffaf067e_1_3959:u8) < 0xa:u8
dsa_R_OF_1_4928:bool =
  high:bool((pad:u8(dsa_mem_ffaf067e_1_3959:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf067e_1_3959:u8) ^ dsa_T_t_1_4926:u8))
dsa_R_AF_1_4929:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_4926:u8 ^ pad:u8(dsa_mem_ffaf067e_1_3959:u8) ^ 0xa:u8))
dsa_R_PF_3_4932:bool =
  ~low:bool(let dsa_T_acc_1_4930:u8 :=
                                        dsa_T_t_1_4926:u8 >> 4:u8 ^
                                        dsa_T_t_1_4926:u8 in
            let dsa_T_acc_2_4931:u8 :=
                                        dsa_T_acc_1_4930:u8 >> 2:u8 ^
                                        dsa_T_acc_1_4930:u8 in
            dsa_T_acc_2_4931:u8 >> 1:u8 ^ dsa_T_acc_2_4931:u8)
dsa_R_SF_1_4933:bool = high:bool(dsa_T_t_1_4926:u8)
dsa_R_ZF_1_4934:bool = 0:u8 == dsa_T_t_1_4926:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x216, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_4935:bool = false
dsa_R_EIP_1_4936:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_4934:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp126"*/
label nocjmp126
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf067e, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_4937:u32 = 0xffaf0676:u32
dsa_R_DF_1_4938:bool = false
dsa_R_EDX_32_1_4939:u32 = 0xffaf067e:u32
dsa_T_t_1_4940:u32 = dsa_R_EDX_32_1_4939:u32 - dsa_R_EBP_32_1_4937:u32
dsa_R_CF_1_4941:bool = dsa_R_EDX_32_1_4939:u32 < dsa_R_EBP_32_1_4937:u32
dsa_R_OF_1_4942:bool =
  high:bool((dsa_R_EDX_32_1_4939:u32 ^ dsa_R_EBP_32_1_4937:u32) &
            (dsa_R_EDX_32_1_4939:u32 ^ dsa_T_t_1_4940:u32))
dsa_R_AF_1_4943:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_4940:u32 ^ dsa_R_EDX_32_1_4939:u32 ^ dsa_R_EBP_32_1_4937:u32))
dsa_R_PF_3_4946:bool =
  ~low:bool(let dsa_T_acc_1_4944:u32 :=
                                         dsa_T_t_1_4940:u32 >> 4:u32 ^
                                         dsa_T_t_1_4940:u32 in
            let dsa_T_acc_2_4945:u32 :=
                                         dsa_T_acc_1_4944:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4944:u32 in
            dsa_T_acc_2_4945:u32 >> 1:u32 ^ dsa_T_acc_2_4945:u32)
dsa_R_SF_1_4947:bool = high:bool(dsa_T_t_1_4940:u32)
dsa_R_ZF_1_4948:bool = 0:u32 == dsa_T_t_1_4940:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf067d, 0, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
  @context "mem32[0xffaf067d]" = 0x35, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_4949:bool = false
dsa_R_AF_1_4950:bool = false
dsa_R_OF_1_4951:bool = false
dsa_R_SF_1_4952:bool = true
dsa_R_DF_1_4953:bool = false
dsa_R_EDX_32_1_4954:u32 = 0xffaf067d:u32
dsa_R_CF_1_4955:bool = false
dsa_R_EFLAGS_1_4956:u32 = 0x286:u32
dsa_R_PF_1_4957:bool = true
dsa_T_t_1_4958:u8 = pad:u8(dsa_mem_ffaf067d_1_4045:u8) - 0xa:u8
dsa_R_CF_1_4959:bool = pad:u8(dsa_mem_ffaf067d_1_4045:u8) < 0xa:u8
dsa_R_OF_1_4960:bool =
  high:bool((pad:u8(dsa_mem_ffaf067d_1_4045:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf067d_1_4045:u8) ^ dsa_T_t_1_4958:u8))
dsa_R_AF_1_4961:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_4958:u8 ^ pad:u8(dsa_mem_ffaf067d_1_4045:u8) ^ 0xa:u8))
dsa_R_PF_3_4964:bool =
  ~low:bool(let dsa_T_acc_1_4962:u8 :=
                                        dsa_T_t_1_4958:u8 >> 4:u8 ^
                                        dsa_T_t_1_4958:u8 in
            let dsa_T_acc_2_4963:u8 :=
                                        dsa_T_acc_1_4962:u8 >> 2:u8 ^
                                        dsa_T_acc_1_4962:u8 in
            dsa_T_acc_2_4963:u8 >> 1:u8 ^ dsa_T_acc_2_4963:u8)
dsa_R_SF_1_4965:bool = high:bool(dsa_T_t_1_4958:u8)
dsa_R_ZF_1_4966:bool = 0:u8 == dsa_T_t_1_4958:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x216, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_4967:bool = false
dsa_R_EIP_1_4968:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_4966:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp127"*/
label nocjmp127
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf067d, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_4969:u32 = 0xffaf0676:u32
dsa_R_DF_1_4970:bool = false
dsa_R_EDX_32_1_4971:u32 = 0xffaf067d:u32
dsa_T_t_1_4972:u32 = dsa_R_EDX_32_1_4971:u32 - dsa_R_EBP_32_1_4969:u32
dsa_R_CF_1_4973:bool = dsa_R_EDX_32_1_4971:u32 < dsa_R_EBP_32_1_4969:u32
dsa_R_OF_1_4974:bool =
  high:bool((dsa_R_EDX_32_1_4971:u32 ^ dsa_R_EBP_32_1_4969:u32) &
            (dsa_R_EDX_32_1_4971:u32 ^ dsa_T_t_1_4972:u32))
dsa_R_AF_1_4975:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_4972:u32 ^ dsa_R_EDX_32_1_4971:u32 ^ dsa_R_EBP_32_1_4969:u32))
dsa_R_PF_3_4978:bool =
  ~low:bool(let dsa_T_acc_1_4976:u32 :=
                                         dsa_T_t_1_4972:u32 >> 4:u32 ^
                                         dsa_T_t_1_4972:u32 in
            let dsa_T_acc_2_4977:u32 :=
                                         dsa_T_acc_1_4976:u32 >> 2:u32 ^
                                         dsa_T_acc_1_4976:u32 in
            dsa_T_acc_2_4977:u32 >> 1:u32 ^ dsa_T_acc_2_4977:u32)
dsa_R_SF_1_4979:bool = high:bool(dsa_T_t_1_4972:u32)
dsa_R_ZF_1_4980:bool = 0:u32 == dsa_T_t_1_4972:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf067c, 0, u32, rd
  @context "R_EFLAGS" = 0x282, 0, u32, wr
  @context "mem32[0xffaf067c]" = 0x35, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_4981:bool = false
dsa_R_AF_1_4982:bool = false
dsa_R_OF_1_4983:bool = false
dsa_R_SF_1_4984:bool = true
dsa_R_DF_1_4985:bool = false
dsa_R_EDX_32_1_4986:u32 = 0xffaf067c:u32
dsa_R_CF_1_4987:bool = false
dsa_R_EFLAGS_1_4988:u32 = 0x282:u32
dsa_R_PF_1_4989:bool = false
dsa_T_t_1_4990:u8 = pad:u8(dsa_mem_ffaf067c_1_4131:u8) - 0xa:u8
dsa_R_CF_1_4991:bool = pad:u8(dsa_mem_ffaf067c_1_4131:u8) < 0xa:u8
dsa_R_OF_1_4992:bool =
  high:bool((pad:u8(dsa_mem_ffaf067c_1_4131:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf067c_1_4131:u8) ^ dsa_T_t_1_4990:u8))
dsa_R_AF_1_4993:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_4990:u8 ^ pad:u8(dsa_mem_ffaf067c_1_4131:u8) ^ 0xa:u8))
dsa_R_PF_3_4996:bool =
  ~low:bool(let dsa_T_acc_1_4994:u8 :=
                                        dsa_T_t_1_4990:u8 >> 4:u8 ^
                                        dsa_T_t_1_4990:u8 in
            let dsa_T_acc_2_4995:u8 :=
                                        dsa_T_acc_1_4994:u8 >> 2:u8 ^
                                        dsa_T_acc_1_4994:u8 in
            dsa_T_acc_2_4995:u8 >> 1:u8 ^ dsa_T_acc_2_4995:u8)
dsa_R_SF_1_4997:bool = high:bool(dsa_T_t_1_4990:u8)
dsa_R_ZF_1_4998:bool = 0:u8 == dsa_T_t_1_4990:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x216, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_4999:bool = false
dsa_R_EIP_1_5000:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_4998:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp128"*/
label nocjmp128
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf067c, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_5001:u32 = 0xffaf0676:u32
dsa_R_DF_1_5002:bool = false
dsa_R_EDX_32_1_5003:u32 = 0xffaf067c:u32
dsa_T_t_1_5004:u32 = dsa_R_EDX_32_1_5003:u32 - dsa_R_EBP_32_1_5001:u32
dsa_R_CF_1_5005:bool = dsa_R_EDX_32_1_5003:u32 < dsa_R_EBP_32_1_5001:u32
dsa_R_OF_1_5006:bool =
  high:bool((dsa_R_EDX_32_1_5003:u32 ^ dsa_R_EBP_32_1_5001:u32) &
            (dsa_R_EDX_32_1_5003:u32 ^ dsa_T_t_1_5004:u32))
dsa_R_AF_1_5007:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_5004:u32 ^ dsa_R_EDX_32_1_5003:u32 ^ dsa_R_EBP_32_1_5001:u32))
dsa_R_PF_3_5010:bool =
  ~low:bool(let dsa_T_acc_1_5008:u32 :=
                                         dsa_T_t_1_5004:u32 >> 4:u32 ^
                                         dsa_T_t_1_5004:u32 in
            let dsa_T_acc_2_5009:u32 :=
                                         dsa_T_acc_1_5008:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5008:u32 in
            dsa_T_acc_2_5009:u32 >> 1:u32 ^ dsa_T_acc_2_5009:u32)
dsa_R_SF_1_5011:bool = high:bool(dsa_T_t_1_5004:u32)
dsa_R_ZF_1_5012:bool = 0:u32 == dsa_T_t_1_5004:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf067b, 0, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
  @context "mem32[0xffaf067b]" = 0x39, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_5013:bool = false
dsa_R_AF_1_5014:bool = false
dsa_R_OF_1_5015:bool = false
dsa_R_SF_1_5016:bool = true
dsa_R_DF_1_5017:bool = false
dsa_R_EDX_32_1_5018:u32 = 0xffaf067b:u32
dsa_R_CF_1_5019:bool = false
dsa_R_EFLAGS_1_5020:u32 = 0x286:u32
dsa_R_PF_1_5021:bool = true
dsa_T_t_1_5022:u8 = pad:u8(dsa_mem_ffaf067b_1_4217:u8) - 0xa:u8
dsa_R_CF_1_5023:bool = pad:u8(dsa_mem_ffaf067b_1_4217:u8) < 0xa:u8
dsa_R_OF_1_5024:bool =
  high:bool((pad:u8(dsa_mem_ffaf067b_1_4217:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf067b_1_4217:u8) ^ dsa_T_t_1_5022:u8))
dsa_R_AF_1_5025:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_5022:u8 ^ pad:u8(dsa_mem_ffaf067b_1_4217:u8) ^ 0xa:u8))
dsa_R_PF_3_5028:bool =
  ~low:bool(let dsa_T_acc_1_5026:u8 :=
                                        dsa_T_t_1_5022:u8 >> 4:u8 ^
                                        dsa_T_t_1_5022:u8 in
            let dsa_T_acc_2_5027:u8 :=
                                        dsa_T_acc_1_5026:u8 >> 2:u8 ^
                                        dsa_T_acc_1_5026:u8 in
            dsa_T_acc_2_5027:u8 >> 1:u8 ^ dsa_T_acc_2_5027:u8)
dsa_R_SF_1_5029:bool = high:bool(dsa_T_t_1_5022:u8)
dsa_R_ZF_1_5030:bool = 0:u8 == dsa_T_t_1_5022:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x212, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_5031:bool = false
dsa_R_EIP_1_5032:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_5030:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp129"*/
label nocjmp129
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf067b, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_5033:u32 = 0xffaf0676:u32
dsa_R_DF_1_5034:bool = false
dsa_R_EDX_32_1_5035:u32 = 0xffaf067b:u32
dsa_T_t_1_5036:u32 = dsa_R_EDX_32_1_5035:u32 - dsa_R_EBP_32_1_5033:u32
dsa_R_CF_1_5037:bool = dsa_R_EDX_32_1_5035:u32 < dsa_R_EBP_32_1_5033:u32
dsa_R_OF_1_5038:bool =
  high:bool((dsa_R_EDX_32_1_5035:u32 ^ dsa_R_EBP_32_1_5033:u32) &
            (dsa_R_EDX_32_1_5035:u32 ^ dsa_T_t_1_5036:u32))
dsa_R_AF_1_5039:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_5036:u32 ^ dsa_R_EDX_32_1_5035:u32 ^ dsa_R_EBP_32_1_5033:u32))
dsa_R_PF_3_5042:bool =
  ~low:bool(let dsa_T_acc_1_5040:u32 :=
                                         dsa_T_t_1_5036:u32 >> 4:u32 ^
                                         dsa_T_t_1_5036:u32 in
            let dsa_T_acc_2_5041:u32 :=
                                         dsa_T_acc_1_5040:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5040:u32 in
            dsa_T_acc_2_5041:u32 >> 1:u32 ^ dsa_T_acc_2_5041:u32)
dsa_R_SF_1_5043:bool = high:bool(dsa_T_t_1_5036:u32)
dsa_R_ZF_1_5044:bool = 0:u32 == dsa_T_t_1_5036:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf067a, 0, u32, rd
  @context "R_EFLAGS" = 0x282, 0, u32, wr
  @context "mem32[0xffaf067a]" = 0x37, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_5045:bool = false
dsa_R_AF_1_5046:bool = false
dsa_R_OF_1_5047:bool = false
dsa_R_SF_1_5048:bool = true
dsa_R_DF_1_5049:bool = false
dsa_R_EDX_32_1_5050:u32 = 0xffaf067a:u32
dsa_R_CF_1_5051:bool = false
dsa_R_EFLAGS_1_5052:u32 = 0x282:u32
dsa_R_PF_1_5053:bool = false
dsa_T_t_1_5054:u8 = pad:u8(dsa_mem_ffaf067a_1_4303:u8) - 0xa:u8
dsa_R_CF_1_5055:bool = pad:u8(dsa_mem_ffaf067a_1_4303:u8) < 0xa:u8
dsa_R_OF_1_5056:bool =
  high:bool((pad:u8(dsa_mem_ffaf067a_1_4303:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf067a_1_4303:u8) ^ dsa_T_t_1_5054:u8))
dsa_R_AF_1_5057:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_5054:u8 ^ pad:u8(dsa_mem_ffaf067a_1_4303:u8) ^ 0xa:u8))
dsa_R_PF_3_5060:bool =
  ~low:bool(let dsa_T_acc_1_5058:u8 :=
                                        dsa_T_t_1_5054:u8 >> 4:u8 ^
                                        dsa_T_t_1_5054:u8 in
            let dsa_T_acc_2_5059:u8 :=
                                        dsa_T_acc_1_5058:u8 >> 2:u8 ^
                                        dsa_T_acc_1_5058:u8 in
            dsa_T_acc_2_5059:u8 >> 1:u8 ^ dsa_T_acc_2_5059:u8)
dsa_R_SF_1_5061:bool = high:bool(dsa_T_t_1_5054:u8)
dsa_R_ZF_1_5062:bool = 0:u8 == dsa_T_t_1_5054:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x216, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_5063:bool = false
dsa_R_EIP_1_5064:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_5062:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp130"*/
label nocjmp130
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf067a, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_5065:u32 = 0xffaf0676:u32
dsa_R_DF_1_5066:bool = false
dsa_R_EDX_32_1_5067:u32 = 0xffaf067a:u32
dsa_T_t_1_5068:u32 = dsa_R_EDX_32_1_5067:u32 - dsa_R_EBP_32_1_5065:u32
dsa_R_CF_1_5069:bool = dsa_R_EDX_32_1_5067:u32 < dsa_R_EBP_32_1_5065:u32
dsa_R_OF_1_5070:bool =
  high:bool((dsa_R_EDX_32_1_5067:u32 ^ dsa_R_EBP_32_1_5065:u32) &
            (dsa_R_EDX_32_1_5067:u32 ^ dsa_T_t_1_5068:u32))
dsa_R_AF_1_5071:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_5068:u32 ^ dsa_R_EDX_32_1_5067:u32 ^ dsa_R_EBP_32_1_5065:u32))
dsa_R_PF_3_5074:bool =
  ~low:bool(let dsa_T_acc_1_5072:u32 :=
                                         dsa_T_t_1_5068:u32 >> 4:u32 ^
                                         dsa_T_t_1_5068:u32 in
            let dsa_T_acc_2_5073:u32 :=
                                         dsa_T_acc_1_5072:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5072:u32 in
            dsa_T_acc_2_5073:u32 >> 1:u32 ^ dsa_T_acc_2_5073:u32)
dsa_R_SF_1_5075:bool = high:bool(dsa_T_t_1_5068:u32)
dsa_R_ZF_1_5076:bool = 0:u32 == dsa_T_t_1_5068:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf0679, 0, u32, rd
  @context "R_EFLAGS" = 0x282, 0, u32, wr
  @context "mem32[0xffaf0679]" = 0x34, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_5077:bool = false
dsa_R_AF_1_5078:bool = false
dsa_R_OF_1_5079:bool = false
dsa_R_SF_1_5080:bool = true
dsa_R_DF_1_5081:bool = false
dsa_R_EDX_32_1_5082:u32 = 0xffaf0679:u32
dsa_R_CF_1_5083:bool = false
dsa_R_EFLAGS_1_5084:u32 = 0x282:u32
dsa_R_PF_1_5085:bool = false
dsa_T_t_1_5086:u8 = pad:u8(dsa_mem_ffaf0679_1_4389:u8) - 0xa:u8
dsa_R_CF_1_5087:bool = pad:u8(dsa_mem_ffaf0679_1_4389:u8) < 0xa:u8
dsa_R_OF_1_5088:bool =
  high:bool((pad:u8(dsa_mem_ffaf0679_1_4389:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf0679_1_4389:u8) ^ dsa_T_t_1_5086:u8))
dsa_R_AF_1_5089:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_5086:u8 ^ pad:u8(dsa_mem_ffaf0679_1_4389:u8) ^ 0xa:u8))
dsa_R_PF_3_5092:bool =
  ~low:bool(let dsa_T_acc_1_5090:u8 :=
                                        dsa_T_t_1_5086:u8 >> 4:u8 ^
                                        dsa_T_t_1_5086:u8 in
            let dsa_T_acc_2_5091:u8 :=
                                        dsa_T_acc_1_5090:u8 >> 2:u8 ^
                                        dsa_T_acc_1_5090:u8 in
            dsa_T_acc_2_5091:u8 >> 1:u8 ^ dsa_T_acc_2_5091:u8)
dsa_R_SF_1_5093:bool = high:bool(dsa_T_t_1_5086:u8)
dsa_R_ZF_1_5094:bool = 0:u8 == dsa_T_t_1_5086:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x212, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_5095:bool = false
dsa_R_EIP_1_5096:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_5094:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp131"*/
label nocjmp131
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf0679, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_5097:u32 = 0xffaf0676:u32
dsa_R_DF_1_5098:bool = false
dsa_R_EDX_32_1_5099:u32 = 0xffaf0679:u32
dsa_T_t_1_5100:u32 = dsa_R_EDX_32_1_5099:u32 - dsa_R_EBP_32_1_5097:u32
dsa_R_CF_1_5101:bool = dsa_R_EDX_32_1_5099:u32 < dsa_R_EBP_32_1_5097:u32
dsa_R_OF_1_5102:bool =
  high:bool((dsa_R_EDX_32_1_5099:u32 ^ dsa_R_EBP_32_1_5097:u32) &
            (dsa_R_EDX_32_1_5099:u32 ^ dsa_T_t_1_5100:u32))
dsa_R_AF_1_5103:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_5100:u32 ^ dsa_R_EDX_32_1_5099:u32 ^ dsa_R_EBP_32_1_5097:u32))
dsa_R_PF_3_5106:bool =
  ~low:bool(let dsa_T_acc_1_5104:u32 :=
                                         dsa_T_t_1_5100:u32 >> 4:u32 ^
                                         dsa_T_t_1_5100:u32 in
            let dsa_T_acc_2_5105:u32 :=
                                         dsa_T_acc_1_5104:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5104:u32 in
            dsa_T_acc_2_5105:u32 >> 1:u32 ^ dsa_T_acc_2_5105:u32)
dsa_R_SF_1_5107:bool = high:bool(dsa_T_t_1_5100:u32)
dsa_R_ZF_1_5108:bool = 0:u32 == dsa_T_t_1_5100:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf0678, 0, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
  @context "mem32[0xffaf0678]" = 0x39, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_5109:bool = false
dsa_R_AF_1_5110:bool = false
dsa_R_OF_1_5111:bool = false
dsa_R_SF_1_5112:bool = true
dsa_R_DF_1_5113:bool = false
dsa_R_EDX_32_1_5114:u32 = 0xffaf0678:u32
dsa_R_CF_1_5115:bool = false
dsa_R_EFLAGS_1_5116:u32 = 0x286:u32
dsa_R_PF_1_5117:bool = true
dsa_T_t_1_5118:u8 = pad:u8(dsa_mem_ffaf0678_1_4475:u8) - 0xa:u8
dsa_R_CF_1_5119:bool = pad:u8(dsa_mem_ffaf0678_1_4475:u8) < 0xa:u8
dsa_R_OF_1_5120:bool =
  high:bool((pad:u8(dsa_mem_ffaf0678_1_4475:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf0678_1_4475:u8) ^ dsa_T_t_1_5118:u8))
dsa_R_AF_1_5121:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_5118:u8 ^ pad:u8(dsa_mem_ffaf0678_1_4475:u8) ^ 0xa:u8))
dsa_R_PF_3_5124:bool =
  ~low:bool(let dsa_T_acc_1_5122:u8 :=
                                        dsa_T_t_1_5118:u8 >> 4:u8 ^
                                        dsa_T_t_1_5118:u8 in
            let dsa_T_acc_2_5123:u8 :=
                                        dsa_T_acc_1_5122:u8 >> 2:u8 ^
                                        dsa_T_acc_1_5122:u8 in
            dsa_T_acc_2_5123:u8 >> 1:u8 ^ dsa_T_acc_2_5123:u8)
dsa_R_SF_1_5125:bool = high:bool(dsa_T_t_1_5118:u8)
dsa_R_ZF_1_5126:bool = 0:u8 == dsa_T_t_1_5118:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x212, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_5127:bool = false
dsa_R_EIP_1_5128:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_5126:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp132"*/
label nocjmp132
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf0678, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_5129:u32 = 0xffaf0676:u32
dsa_R_DF_1_5130:bool = false
dsa_R_EDX_32_1_5131:u32 = 0xffaf0678:u32
dsa_T_t_1_5132:u32 = dsa_R_EDX_32_1_5131:u32 - dsa_R_EBP_32_1_5129:u32
dsa_R_CF_1_5133:bool = dsa_R_EDX_32_1_5131:u32 < dsa_R_EBP_32_1_5129:u32
dsa_R_OF_1_5134:bool =
  high:bool((dsa_R_EDX_32_1_5131:u32 ^ dsa_R_EBP_32_1_5129:u32) &
            (dsa_R_EDX_32_1_5131:u32 ^ dsa_T_t_1_5132:u32))
dsa_R_AF_1_5135:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_5132:u32 ^ dsa_R_EDX_32_1_5131:u32 ^ dsa_R_EBP_32_1_5129:u32))
dsa_R_PF_3_5138:bool =
  ~low:bool(let dsa_T_acc_1_5136:u32 :=
                                         dsa_T_t_1_5132:u32 >> 4:u32 ^
                                         dsa_T_t_1_5132:u32 in
            let dsa_T_acc_2_5137:u32 :=
                                         dsa_T_acc_1_5136:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5136:u32 in
            dsa_T_acc_2_5137:u32 >> 1:u32 ^ dsa_T_acc_2_5137:u32)
dsa_R_SF_1_5139:bool = high:bool(dsa_T_t_1_5132:u32)
dsa_R_ZF_1_5140:bool = 0:u32 == dsa_T_t_1_5132:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf0677, 0, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
  @context "mem32[0xffaf0677]" = 0x30, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_5141:bool = false
dsa_R_AF_1_5142:bool = false
dsa_R_OF_1_5143:bool = false
dsa_R_SF_1_5144:bool = true
dsa_R_DF_1_5145:bool = false
dsa_R_EDX_32_1_5146:u32 = 0xffaf0677:u32
dsa_R_CF_1_5147:bool = false
dsa_R_EFLAGS_1_5148:u32 = 0x286:u32
dsa_R_PF_1_5149:bool = true
dsa_T_t_1_5150:u8 = pad:u8(dsa_mem_ffaf0677_1_4561:u8) - 0xa:u8
dsa_R_CF_1_5151:bool = pad:u8(dsa_mem_ffaf0677_1_4561:u8) < 0xa:u8
dsa_R_OF_1_5152:bool =
  high:bool((pad:u8(dsa_mem_ffaf0677_1_4561:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf0677_1_4561:u8) ^ dsa_T_t_1_5150:u8))
dsa_R_AF_1_5153:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_5150:u8 ^ pad:u8(dsa_mem_ffaf0677_1_4561:u8) ^ 0xa:u8))
dsa_R_PF_3_5156:bool =
  ~low:bool(let dsa_T_acc_1_5154:u8 :=
                                        dsa_T_t_1_5150:u8 >> 4:u8 ^
                                        dsa_T_t_1_5150:u8 in
            let dsa_T_acc_2_5155:u8 :=
                                        dsa_T_acc_1_5154:u8 >> 2:u8 ^
                                        dsa_T_acc_1_5154:u8 in
            dsa_T_acc_2_5155:u8 >> 1:u8 ^ dsa_T_acc_2_5155:u8)
dsa_R_SF_1_5157:bool = high:bool(dsa_T_t_1_5150:u8)
dsa_R_ZF_1_5158:bool = 0:u8 == dsa_T_t_1_5150:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x212, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_5159:bool = false
dsa_R_EIP_1_5160:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_5158:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp133"*/
label nocjmp133
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf0677, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_5161:u32 = 0xffaf0676:u32
dsa_R_DF_1_5162:bool = false
dsa_R_EDX_32_1_5163:u32 = 0xffaf0677:u32
dsa_T_t_1_5164:u32 = dsa_R_EDX_32_1_5163:u32 - dsa_R_EBP_32_1_5161:u32
dsa_R_CF_1_5165:bool = dsa_R_EDX_32_1_5163:u32 < dsa_R_EBP_32_1_5161:u32
dsa_R_OF_1_5166:bool =
  high:bool((dsa_R_EDX_32_1_5163:u32 ^ dsa_R_EBP_32_1_5161:u32) &
            (dsa_R_EDX_32_1_5163:u32 ^ dsa_T_t_1_5164:u32))
dsa_R_AF_1_5167:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_5164:u32 ^ dsa_R_EDX_32_1_5163:u32 ^ dsa_R_EBP_32_1_5161:u32))
dsa_R_PF_3_5170:bool =
  ~low:bool(let dsa_T_acc_1_5168:u32 :=
                                         dsa_T_t_1_5164:u32 >> 4:u32 ^
                                         dsa_T_t_1_5164:u32 in
            let dsa_T_acc_2_5169:u32 :=
                                         dsa_T_acc_1_5168:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5168:u32 in
            dsa_T_acc_2_5169:u32 >> 1:u32 ^ dsa_T_acc_2_5169:u32)
dsa_R_SF_1_5171:bool = high:bool(dsa_T_t_1_5164:u32)
dsa_R_ZF_1_5172:bool = 0:u32 == dsa_T_t_1_5164:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x282, 0, u32, wr
  @context "mem32[0xffaf0676]" = 0x31, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_5173:bool = false
dsa_R_AF_1_5174:bool = false
dsa_R_OF_1_5175:bool = false
dsa_R_SF_1_5176:bool = true
dsa_R_DF_1_5177:bool = false
dsa_R_EDX_32_1_5178:u32 = 0xffaf0676:u32
dsa_R_CF_1_5179:bool = false
dsa_R_EFLAGS_1_5180:u32 = 0x282:u32
dsa_R_PF_1_5181:bool = false
dsa_T_t_1_5182:u8 = pad:u8(dsa_mem_ffaf0676_1_4647:u8) - 0xa:u8
dsa_R_CF_1_5183:bool = pad:u8(dsa_mem_ffaf0676_1_4647:u8) < 0xa:u8
dsa_R_OF_1_5184:bool =
  high:bool((pad:u8(dsa_mem_ffaf0676_1_4647:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf0676_1_4647:u8) ^ dsa_T_t_1_5182:u8))
dsa_R_AF_1_5185:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_5182:u8 ^ pad:u8(dsa_mem_ffaf0676_1_4647:u8) ^ 0xa:u8))
dsa_R_PF_3_5188:bool =
  ~low:bool(let dsa_T_acc_1_5186:u8 :=
                                        dsa_T_t_1_5182:u8 >> 4:u8 ^
                                        dsa_T_t_1_5182:u8 in
            let dsa_T_acc_2_5187:u8 :=
                                        dsa_T_acc_1_5186:u8 >> 2:u8 ^
                                        dsa_T_acc_1_5186:u8 in
            dsa_T_acc_2_5187:u8 >> 1:u8 ^ dsa_T_acc_2_5187:u8)
dsa_R_SF_1_5189:bool = high:bool(dsa_T_t_1_5182:u8)
dsa_R_ZF_1_5190:bool = 0:u8 == dsa_T_t_1_5182:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x216, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_5191:bool = false
dsa_R_EIP_1_5192:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_5190:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp134"*/
label nocjmp134
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf0676, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_5193:u32 = 0xffaf0676:u32
dsa_R_DF_1_5194:bool = false
dsa_R_EDX_32_1_5195:u32 = 0xffaf0676:u32
dsa_T_t_1_5196:u32 = dsa_R_EDX_32_1_5195:u32 - dsa_R_EBP_32_1_5193:u32
dsa_R_CF_1_5197:bool = dsa_R_EDX_32_1_5195:u32 < dsa_R_EBP_32_1_5193:u32
dsa_R_OF_1_5198:bool =
  high:bool((dsa_R_EDX_32_1_5195:u32 ^ dsa_R_EBP_32_1_5193:u32) &
            (dsa_R_EDX_32_1_5195:u32 ^ dsa_T_t_1_5196:u32))
dsa_R_AF_1_5199:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_5196:u32 ^ dsa_R_EDX_32_1_5195:u32 ^ dsa_R_EBP_32_1_5193:u32))
dsa_R_PF_3_5202:bool =
  ~low:bool(let dsa_T_acc_1_5200:u32 :=
                                         dsa_T_t_1_5196:u32 >> 4:u32 ^
                                         dsa_T_t_1_5196:u32 in
            let dsa_T_acc_2_5201:u32 :=
                                         dsa_T_acc_1_5200:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5200:u32 in
            dsa_T_acc_2_5201:u32 >> 1:u32 ^ dsa_T_acc_2_5201:u32)
dsa_R_SF_1_5203:bool = high:bool(dsa_T_t_1_5196:u32)
dsa_R_ZF_1_5204:bool = 0:u32 == dsa_T_t_1_5196:u32
addr 0xdcf3cc3a @asm "movs   WORD PTR es:[edi],WORD PTR ds:[esi]" @tid "0"
  @context "R_EDI_32" = 0xdcb9d00c, 0, u32, rd
  @context "R_ESI_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x203, 0, u32, rd
  @context "mem32[0xffaf0676]" = 0x31, -1, u8, rd
  @context "mem32[0xffaf0677]" = 0x30, -1, u8, rd
  @context "mem32[0xdcb9d00c]" = 0x31, 0, u8, wr
  @context "mem32[0xdcb9d00d]" = 0x34, 0, u8, wr
label pc_0xdcf3cc3a
dsa_mem_dcb9d00c_1_5205:u8 = low:u8(0x31:u8)
dsa_mem_dcb9d00d_1_5206:u8 = low:u8(0x34:u8)
dsa_R_ZF_1_5207:bool = false
dsa_R_ESI_32_1_5208:u32 = 0xffaf0676:u32
dsa_R_AF_1_5209:bool = false
dsa_R_OF_1_5210:bool = false
dsa_R_SF_1_5211:bool = false
dsa_R_DF_1_5212:bool = false
dsa_R_EDI_32_1_5213:u32 = 0xdcb9d00c:u32
dsa_R_CF_1_5214:bool = true
dsa_R_EFLAGS_1_5215:u32 = 0x203:u32
dsa_R_PF_1_5216:bool = false
dsa_mem_dcb9d00c_1_5217:u8 =
  low:u8(pad:u16(dsa_mem_ffaf0677_1_4561:u8) << 8:u16 |
         pad:u16(dsa_mem_ffaf0676_1_4647:u8))
dsa_mem_dcb9d00d_1_5218:u8 =
  low:u8((pad:u16(dsa_mem_ffaf0677_1_4561:u8) << 8:u16 |
         pad:u16(dsa_mem_ffaf0676_1_4647:u8)) >> 8:u16)
dsa_R_ESI_32_1_5219:u32 =
  dsa_R_ESI_32_1_5208:u32 +
  (if dsa_R_DF_1_5212:bool == false then 1:u32 else -1:u32) * 2:u32
dsa_R_EDI_32_1_5220:u32 =
  dsa_R_EDI_32_1_5213:u32 +
  (if dsa_R_DF_1_5212:bool == false then 1:u32 else -1:u32) * 2:u32
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xdcb9d00e, 0, u32, rd
  @context "R_ESI_32" = 0xffaf0678, 0, u32, rd
  @context "R_ECX_32" = 0x2, 0, u32, rw
  @context "R_EFLAGS" = 0x203, 0, u32, rd
  @context "mem32[0xffaf0678]" = 0x39, -1, u8, rd
  @context "mem32[0xffaf0679]" = 0x34, -1, u8, rd
  @context "mem32[0xffaf067a]" = 0x37, -1, u8, rd
  @context "mem32[0xffaf067b]" = 0x39, -1, u8, rd
  @context "mem32[0xdcb9d00e]" = 0x20, 0, u8, wr
  @context "mem32[0xdcb9d00f]" = 0x3c, 0, u8, wr
  @context "mem32[0xdcb9d010]" = 0x20, 0, u8, wr
  @context "mem32[0xdcb9d011]" = 0x31, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_dcb9d010_1_5221:u8 = low:u8(0x20:u8)
dsa_mem_dcb9d011_1_5222:u8 = low:u8(0x31:u8)
dsa_mem_dcb9d00e_1_5223:u8 = low:u8(0x20:u8)
dsa_mem_dcb9d00f_1_5224:u8 = low:u8(0x3c:u8)
dsa_R_ZF_1_5225:bool = false
dsa_R_ESI_32_1_5226:u32 = 0xffaf0678:u32
dsa_R_AF_1_5227:bool = false
dsa_R_OF_1_5228:bool = false
dsa_R_ECX_32_1_5229:u32 = 2:u32
dsa_R_SF_1_5230:bool = false
dsa_R_DF_1_5231:bool = false
dsa_R_EDI_32_1_5232:u32 = 0xdcb9d00e:u32
dsa_R_CF_1_5233:bool = true
dsa_R_EFLAGS_1_5234:u32 = 0x203:u32
dsa_R_PF_1_5235:bool = false
assert ~(dsa_R_ECX_32_1_5229:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp136"*/
label nocjmp136
dsa_mem_dcb9d00e_1_5236:u8 =
  low:u8(pad:u32(dsa_mem_ffaf067b_1_4217:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067a_1_4303:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf0679_1_4389:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf0678_1_4475:u8))))
dsa_mem_dcb9d00f_1_5237:u8 =
  low:u8((pad:u32(dsa_mem_ffaf067b_1_4217:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067a_1_4303:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf0679_1_4389:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf0678_1_4475:u8)))) >> 8:u32)
dsa_mem_dcb9d010_1_5238:u8 =
  low:u8((pad:u32(dsa_mem_ffaf067b_1_4217:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067a_1_4303:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf0679_1_4389:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf0678_1_4475:u8)))) >> 0x10:u32)
dsa_mem_dcb9d011_1_5239:u8 =
  low:u8((pad:u32(dsa_mem_ffaf067b_1_4217:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067a_1_4303:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf0679_1_4389:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf0678_1_4475:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_5240:u32 =
  dsa_R_ESI_32_1_5226:u32 +
  (if dsa_R_DF_1_5231:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_5241:u32 =
  dsa_R_EDI_32_1_5232:u32 +
  (if dsa_R_DF_1_5231:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_5242:u32 = dsa_R_ECX_32_1_5229:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_5242:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp135"*/
label nocjmp135
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xdcb9d012, 0, u32, rd
  @context "R_ESI_32" = 0xffaf067c, 0, u32, rd
  @context "R_ECX_32" = 0x1, -1, u32, rw
  @context "R_EFLAGS" = 0x203, 0, u32, rd
  @context "mem32[0xffaf067c]" = 0x35, -1, u8, rd
  @context "mem32[0xffaf067d]" = 0x35, -1, u8, rd
  @context "mem32[0xffaf067e]" = 0x38, -1, u8, rd
  @context "mem32[0xffaf067f]" = 0x35, -1, u8, rd
  @context "mem32[0xdcb9d012]" = 0x30, 0, u8, wr
  @context "mem32[0xdcb9d013]" = 0x32, 0, u8, wr
  @context "mem32[0xdcb9d014]" = 0x34, 0, u8, wr
  @context "mem32[0xdcb9d015]" = 0xa, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_dcb9d013_1_5243:u8 = low:u8(0x32:u8)
dsa_mem_dcb9d012_1_5244:u8 = low:u8(0x30:u8)
dsa_mem_dcb9d015_1_5245:u8 = low:u8(0xa:u8)
dsa_mem_dcb9d014_1_5246:u8 = low:u8(0x34:u8)
dsa_R_ZF_1_5247:bool = false
dsa_R_ESI_32_1_5248:u32 = 0xffaf067c:u32
dsa_R_AF_1_5249:bool = false
dsa_R_OF_1_5250:bool = false
dsa_R_SF_1_5251:bool = false
dsa_R_DF_1_5252:bool = false
dsa_R_EDI_32_1_5253:u32 = 0xdcb9d012:u32
dsa_R_CF_1_5254:bool = true
dsa_R_EFLAGS_1_5255:u32 = 0x203:u32
dsa_R_PF_1_5256:bool = false
assert ~(dsa_R_ECX_32_1_5242:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp138"*/
label nocjmp138
dsa_mem_dcb9d012_1_5257:u8 =
  low:u8(pad:u32(dsa_mem_ffaf067f_1_3873:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067e_1_3959:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf067d_1_4045:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf067c_1_4131:u8))))
dsa_mem_dcb9d013_1_5258:u8 =
  low:u8((pad:u32(dsa_mem_ffaf067f_1_3873:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067e_1_3959:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf067d_1_4045:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf067c_1_4131:u8)))) >> 8:u32)
dsa_mem_dcb9d014_1_5259:u8 =
  low:u8((pad:u32(dsa_mem_ffaf067f_1_3873:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067e_1_3959:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf067d_1_4045:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf067c_1_4131:u8)))) >> 0x10:u32)
dsa_mem_dcb9d015_1_5260:u8 =
  low:u8((pad:u32(dsa_mem_ffaf067f_1_3873:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067e_1_3959:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf067d_1_4045:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf067c_1_4131:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_5261:u32 =
  dsa_R_ESI_32_1_5248:u32 +
  (if dsa_R_DF_1_5252:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_5262:u32 =
  dsa_R_EDI_32_1_5253:u32 +
  (if dsa_R_DF_1_5252:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_5263:u32 = dsa_R_ECX_32_1_5242:u32 - 1:u32
assert dsa_R_ECX_32_1_5263:u32 == 0:u32
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp137"*/
addr 0xdcf3ef8b @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x0, -1, u32, wr
  @context "R_EDX_32" = 0x2525, 0, u32, rd
label pc_0xdcf3ef8b
dsa_R_EDX_32_1_5264:u32 = 0x2525:u32
dsa_R_ECX_32_1_5265:u32 = dsa_R_EDX_32_1_5264:u32
addr 0xdcf03ae2 @asm "mov    DWORD PTR [ebp-0x4b8],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "mem32[0xffaf01e0]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf01e1]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf01e2]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf01e3]" = 0x41, -1, u8, wr
label pc_0xdcf03ae2
dsa_R_EBP_32_1_5266:u32 = 0xffaf0698:u32
dsa_mem_ffaf01e0_1_5267:u8 = low:u8(0:u32)
dsa_mem_ffaf01e1_1_5268:u8 = low:u8(0:u32 >> 8:u32)
dsa_mem_ffaf01e2_1_5269:u8 = low:u8(0:u32 >> 0x10:u32)
dsa_mem_ffaf01e3_1_5270:u8 = low:u8(0:u32 >> 0x18:u32)
addr 0xdcf03aec @asm "mov    DWORD PTR [ebp-0x4bc],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "mem32[0xffaf01dc]" = 0x0, -1, u8, wr
  @context "mem32[0xffaf01dd]" = 0x0, -1, u8, wr
  @context "mem32[0xffaf01de]" = 0x0, -1, u8, wr
  @context "mem32[0xffaf01df]" = 0x0, -1, u8, wr
label pc_0xdcf03aec
dsa_R_EBP_32_1_5271:u32 = 0xffaf0698:u32
dsa_mem_ffaf01dc_1_5272:u8 = low:u8(0:u32)
dsa_mem_ffaf01dd_1_5273:u8 = low:u8(0:u32 >> 8:u32)
dsa_mem_ffaf01de_1_5274:u8 = low:u8(0:u32 >> 0x10:u32)
dsa_mem_ffaf01df_1_5275:u8 = low:u8(0:u32 >> 0x18:u32)
addr 0xdcf07865 @asm "mov    eax,DWORD PTR [eax]" @tid "0"
  @context "R_EAX_32" = 0xffaf06c8, 0, u32, wr
  @context "R_EAX_32" = 0xffaf06c8, 0, u32, rd
  @context "mem32[0xffaf06c8]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf06c9]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf06ca]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf06cb]" = 0x41, -1, u8, rd
label pc_0xdcf07865
dsa_R_EAX_32_1_5276:u32 = 0xffaf06c8:u32
dsa_R_EAX_32_1_5277:u32 =
  pad:u32(dsa_mem_ffaf06cb_1_3667:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf06ca_1_3666:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf06c9_1_3665:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf06c8_1_3664:u8)))
addr 0xdcf0781b @asm "mov    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0xdcf040f1, 0, u32, wr
  @context "R_EAX_32" = 0x41414141, -1, u32, rd
label pc_0xdcf0781b
dsa_R_ECX_32_1_5278:u32 = 0xdcf040f1:u32
dsa_R_ECX_32_1_5279:u32 = dsa_R_EAX_32_1_5277:u32
addr 0xdcf0781d @asm "mov    edx,eax" @tid "0"
  @context "R_EDX_32" = 0x44, 0, u32, wr
  @context "R_EAX_32" = 0x41414141, -1, u32, rd
label pc_0xdcf0781d
dsa_R_EDX_32_1_5280:u32 = 0x44:u32
dsa_R_EDX_32_1_5281:u32 = dsa_R_EAX_32_1_5277:u32
addr 0xdcf0781f @asm "shr    ecx,0x1f" @tid "0"
  @context "R_ECX_32" = 0x41414141, -1, u32, rw
  @context "R_EFLAGS" = 0x246, 0, u32, wr
label pc_0xdcf0781f
dsa_R_ZF_1_5282:bool = true
dsa_R_AF_1_5283:bool = false
dsa_R_OF_1_5284:bool = false
dsa_R_SF_1_5285:bool = false
dsa_R_DF_1_5286:bool = false
dsa_R_CF_1_5287:bool = false
dsa_R_EFLAGS_1_5288:u32 = 0x246:u32
dsa_R_PF_1_5289:bool = true
dsa_T_origDEST_1_5290:u32 = dsa_R_ECX_32_1_5279:u32
dsa_T_origCOUNT_1_5291:u32 = 0x1f:u32
dsa_R_ECX_32_1_5292:u32 = dsa_R_ECX_32_1_5279:u32 >> 0x1f:u32
dsa_R_CF_1_5293:bool =
  if dsa_T_origCOUNT_1_5291:u32 == 0:u32 then dsa_R_CF_1_5287:bool else
  high:bool(dsa_T_origDEST_1_5290:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_5291:u32)
dsa_R_OF_1_5294:bool =
  if dsa_T_origCOUNT_1_5291:u32 == 0:u32 then dsa_R_OF_1_5284:bool else
  if dsa_T_origCOUNT_1_5291:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_5290:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_5295:bool =
  if dsa_T_origCOUNT_1_5291:u32 == 0:u32 then dsa_R_SF_1_5285:bool else
  high:bool(dsa_R_ECX_32_1_5292:u32)
dsa_R_ZF_1_5296:bool =
  if dsa_T_origCOUNT_1_5291:u32 == 0:u32 then dsa_R_ZF_1_5282:bool else
  0:u32 == dsa_R_ECX_32_1_5292:u32
dsa_R_PF_3_5299:bool =
  if dsa_T_origCOUNT_1_5291:u32 == 0:u32 then dsa_R_PF_1_5289:bool else
  ~low:bool(let dsa_T_acc_1_5297:u32 :=
                                         dsa_R_ECX_32_1_5292:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_5292:u32 in
            let dsa_T_acc_2_5298:u32 :=
                                         dsa_T_acc_1_5297:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5297:u32 in
            dsa_T_acc_2_5298:u32 >> 1:u32 ^ dsa_T_acc_2_5298:u32)
dsa_R_AF_1_5300:bool =
  if dsa_T_origCOUNT_1_5291:u32 == 0:u32 then dsa_R_AF_1_5283:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf07822 @asm "neg    edx" @tid "0"
  @context "R_EDX_32" = 0x41414141, -1, u32, rw
  @context "R_EFLAGS" = 0x247, -1, u32, wr
label pc_0xdcf07822
dsa_R_DF_1_5301:bool = false
dsa_T_t_1_5302:u32 = dsa_R_EDX_32_1_5281:u32
dsa_R_EDX_32_1_5303:u32 = 0:u32 - dsa_R_EDX_32_1_5281:u32
dsa_R_CF_1_5304:bool = if dsa_T_t_1_5302:u32 == 0:u32 then false else true
dsa_R_OF_1_5305:bool =
  if dsa_T_t_1_5302:u32 == 0x80000000:u32 then true else false
dsa_R_AF_1_5306:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_EDX_32_1_5303:u32 ^ dsa_T_t_1_5302:u32 ^ 0:u32))
dsa_R_PF_3_5309:bool =
  ~low:bool(let dsa_T_acc_1_5307:u32 :=
                                         dsa_R_EDX_32_1_5303:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_5303:u32 in
            let dsa_T_acc_2_5308:u32 :=
                                         dsa_T_acc_1_5307:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5307:u32 in
            dsa_T_acc_2_5308:u32 >> 1:u32 ^ dsa_T_acc_2_5308:u32)
dsa_R_SF_1_5310:bool = high:bool(dsa_R_EDX_32_1_5303:u32)
dsa_R_ZF_1_5311:bool = 0:u32 == dsa_R_EDX_32_1_5303:u32
addr 0xdcf07824 @asm "test   ecx,ecx" @tid "0"
  @context "R_ECX_32" = 0x0, -1, u32, rd
  @context "R_ECX_32" = 0x0, -1, u32, rd
  @context "R_EFLAGS" = 0x293, -1, u32, wr
label pc_0xdcf07824
dsa_R_DF_1_5312:bool = false
dsa_T_t_1_5313:u32 = dsa_R_ECX_32_1_5292:u32 & dsa_R_ECX_32_1_5292:u32
dsa_R_OF_1_5314:bool = false
dsa_R_CF_1_5315:bool = false
dsa_R_AF_1_5316:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_5319:bool =
  ~low:bool(let dsa_T_acc_1_5317:u32 :=
                                         dsa_T_t_1_5313:u32 >> 4:u32 ^
                                         dsa_T_t_1_5313:u32 in
            let dsa_T_acc_2_5318:u32 :=
                                         dsa_T_acc_1_5317:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5317:u32 in
            dsa_T_acc_2_5318:u32 >> 1:u32 ^ dsa_T_acc_2_5318:u32)
dsa_R_SF_1_5320:bool = high:bool(dsa_T_t_1_5313:u32)
dsa_R_ZF_1_5321:bool = 0:u32 == dsa_T_t_1_5313:u32
addr 0xdcf07826 @asm "cmovne eax,edx" @tid "0"
  @context "R_EAX_32" = 0x41414141, -1, u32, wr
  @context "R_EDX_32" = 0xbebebebf, -1, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, rd
label pc_0xdcf07826
dsa_R_DF_1_5322:bool = false
dsa_R_EAX_32_1_5323:u32 =
  if ~dsa_R_ZF_1_5321:bool then dsa_R_EDX_32_1_5303:u32 else
  dsa_R_EAX_32_1_5277:u32
addr 0xdcf07829 @asm "mov    DWORD PTR [ebp-0x4bc],ecx" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_ECX_32" = 0x0, -1, u32, rd
  @context "mem32[0xffaf01dc]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf01dd]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf01de]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf01df]" = 0x0, 0, u8, wr
label pc_0xdcf07829
dsa_mem_ffaf01dc_1_5324:u8 = low:u8(0:u8)
dsa_mem_ffaf01de_1_5325:u8 = low:u8(0:u8)
dsa_mem_ffaf01dd_1_5326:u8 = low:u8(0:u8)
dsa_mem_ffaf01df_1_5327:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_5328:u32 = 0xffaf0698:u32
dsa_mem_ffaf01dc_1_5329:u8 = low:u8(dsa_R_ECX_32_1_5292:u32)
dsa_mem_ffaf01dd_1_5330:u8 = low:u8(dsa_R_ECX_32_1_5292:u32 >> 8:u32)
dsa_mem_ffaf01de_1_5331:u8 = low:u8(dsa_R_ECX_32_1_5292:u32 >> 0x10:u32)
dsa_mem_ffaf01df_1_5332:u8 = low:u8(dsa_R_ECX_32_1_5292:u32 >> 0x18:u32)
addr 0xdcf0782f @asm "mov    DWORD PTR [ebp-0x4b8],eax" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EAX_32" = 0x41414141, -1, u32, rd
  @context "mem32[0xffaf01e0]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf01e1]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf01e2]" = 0x0, 0, u8, wr
  @context "mem32[0xffaf01e3]" = 0x0, 0, u8, wr
label pc_0xdcf0782f
dsa_mem_ffaf01e1_1_5333:u8 = low:u8(0:u8)
dsa_mem_ffaf01e0_1_5334:u8 = low:u8(0:u8)
dsa_mem_ffaf01e3_1_5335:u8 = low:u8(0:u8)
dsa_mem_ffaf01e2_1_5336:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_5337:u32 = 0xffaf0698:u32
dsa_mem_ffaf01e0_1_5338:u8 = low:u8(dsa_R_EAX_32_1_5323:u32)
dsa_mem_ffaf01e1_1_5339:u8 = low:u8(dsa_R_EAX_32_1_5323:u32 >> 8:u32)
dsa_mem_ffaf01e2_1_5340:u8 = low:u8(dsa_R_EAX_32_1_5323:u32 >> 0x10:u32)
dsa_mem_ffaf01e3_1_5341:u8 = low:u8(dsa_R_EAX_32_1_5323:u32 >> 0x18:u32)
addr 0xdcf04456 @asm "cmp    DWORD PTR [ebp-0x49c],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
  @context "mem32[0xffaf01fc]" = 0xff, 0, u8, rd
  @context "mem32[0xffaf01fd]" = 0xff, 0, u8, rd
  @context "mem32[0xffaf01fe]" = 0xff, 0, u8, rd
  @context "mem32[0xffaf01ff]" = 0xff, 0, u8, rd
label pc_0xdcf04456
dsa_mem_ffaf01fe_1_5342:u8 = low:u8(-1:u8)
dsa_mem_ffaf01fc_1_5343:u8 = low:u8(-1:u8)
dsa_mem_ffaf01fd_1_5344:u8 = low:u8(-1:u8)
dsa_mem_ffaf01ff_1_5345:u8 = low:u8(-1:u8)
dsa_R_EBP_32_1_5346:u32 = 0xffaf0698:u32
dsa_R_DF_1_5347:bool = false
dsa_T_t_1_5348:u32 =
  (pad:u32(dsa_mem_ffaf01ff_1_5345:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01fe_1_5342:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01fd_1_5344:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01fc_1_5343:u8)))) - 0:u32
dsa_R_CF_1_5349:bool =
  (pad:u32(dsa_mem_ffaf01ff_1_5345:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01fe_1_5342:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01fd_1_5344:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01fc_1_5343:u8)))) < 0:u32
dsa_R_OF_1_5350:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01ff_1_5345:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01fe_1_5342:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01fd_1_5344:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01fc_1_5343:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01ff_1_5345:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01fe_1_5342:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01fd_1_5344:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01fc_1_5343:u8)))) ^ dsa_T_t_1_5348:u32))
dsa_R_AF_1_5351:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_5348:u32 ^
   (pad:u32(dsa_mem_ffaf01ff_1_5345:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01fe_1_5342:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01fd_1_5344:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01fc_1_5343:u8)))) ^ 0:u32))
dsa_R_PF_3_5354:bool =
  ~low:bool(let dsa_T_acc_1_5352:u32 :=
                                         dsa_T_t_1_5348:u32 >> 4:u32 ^
                                         dsa_T_t_1_5348:u32 in
            let dsa_T_acc_2_5353:u32 :=
                                         dsa_T_acc_1_5352:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5352:u32 in
            dsa_T_acc_2_5353:u32 >> 1:u32 ^ dsa_T_acc_2_5353:u32)
dsa_R_SF_1_5355:bool = high:bool(dsa_T_t_1_5348:u32)
dsa_R_ZF_1_5356:bool = 0:u32 == dsa_T_t_1_5348:u32
addr 0xdcf068fd @asm "xor    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x41414141, -1, u32, wr
  @context "R_EAX_32" = 0x41414141, -1, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
label pc_0xdcf068fd
dsa_R_ZF_1_5357:bool = false
dsa_R_AF_1_5358:bool = false
dsa_R_OF_1_5359:bool = false
dsa_R_SF_1_5360:bool = true
dsa_R_DF_1_5361:bool = false
dsa_R_CF_1_5362:bool = false
dsa_R_EFLAGS_1_5363:u32 = 0x286:u32
dsa_R_PF_1_5364:bool = true
dsa_R_EAX_32_1_5365:u32 = 0:u32
dsa_R_AF_1_5366:bool = unknown "AF is undefined after xor":bool
dsa_R_ZF_1_5367:bool = true
dsa_R_PF_1_5368:bool = true
dsa_R_OF_1_5369:bool = false
dsa_R_CF_1_5370:bool = false
dsa_R_SF_1_5371:bool = false
addr 0xdcf0691b @asm "mov    eax,DWORD PTR [ebp-0x4b8]" @tid "0"
  @context "R_EAX_32" = 0xa, 0, u32, wr
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "mem32[0xffaf01e0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e3]" = 0x41, -1, u8, rd
label pc_0xdcf0691b
dsa_R_EBP_32_1_5372:u32 = 0xffaf0698:u32
dsa_R_EAX_32_1_5373:u32 = 0xa:u32
dsa_R_EAX_32_1_5374:u32 =
  pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))
addr 0xdcf06921 @asm "mov    DWORD PTR [esp],eax" @tid "0"
  @context "R_ESP_32" = 0xffaf0180, 0, u32, rd
  @context "R_EAX_32" = 0x41414141, -1, u32, rd
  @context "mem32[0xffaf0180]" = 0xc0, 0, u8, wr
  @context "mem32[0xffaf0181]" = 0xda, 0, u8, wr
  @context "mem32[0xffaf0182]" = 0x6, 0, u8, wr
  @context "mem32[0xffaf0183]" = 0xdd, 0, u8, wr
label pc_0xdcf06921
dsa_mem_ffaf0181_1_5375:u8 = low:u8(0xda:u8)
dsa_mem_ffaf0183_1_5376:u8 = low:u8(0xdd:u8)
dsa_mem_ffaf0180_1_5377:u8 = low:u8(0xc0:u8)
dsa_mem_ffaf0182_1_5378:u8 = low:u8(6:u8)
dsa_R_ESP_32_1_5379:u32 = 0xffaf0180:u32
dsa_mem_ffaf0180_1_5380:u8 = low:u8(dsa_R_EAX_32_1_5374:u32)
dsa_mem_ffaf0181_1_5381:u8 = low:u8(dsa_R_EAX_32_1_5374:u32 >> 8:u32)
dsa_mem_ffaf0182_1_5382:u8 = low:u8(dsa_R_EAX_32_1_5374:u32 >> 0x10:u32)
dsa_mem_ffaf0183_1_5383:u8 = low:u8(dsa_R_EAX_32_1_5374:u32 >> 0x18:u32)
addr 0xdcf03174 @asm "mov    eax,DWORD PTR [esp+0x20]" @tid "0"
  @context "R_EAX_32" = 0x41414141, -1, u32, wr
  @context "R_ESP_32" = 0xffaf016c, 0, u32, rd
  @context "mem32[0xffaf018c]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf018d]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf018e]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf018f]" = 0x0, 0, u8, rd
label pc_0xdcf03174
dsa_mem_ffaf018d_1_5384:u8 = low:u8(0:u8)
dsa_mem_ffaf018e_1_5385:u8 = low:u8(0:u8)
dsa_mem_ffaf018f_1_5386:u8 = low:u8(0:u8)
dsa_mem_ffaf018c_1_5387:u8 = low:u8(0:u8)
dsa_R_ESP_32_1_5388:u32 = 0xffaf016c:u32
dsa_R_EAX_32_1_5389:u32 =
  pad:u32(dsa_mem_ffaf018f_1_5386:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf018e_1_5385:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf018d_1_5384:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf018c_1_5387:u8)))
addr 0xdcf03187 @asm "mov    ecx,DWORD PTR [esp+0x14]" @tid "0"
  @context "R_ECX_32" = 0x0, -1, u32, wr
  @context "R_ESP_32" = 0xffaf016c, 0, u32, rd
  @context "mem32[0xffaf0180]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0181]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0182]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0183]" = 0x41, -1, u8, rd
label pc_0xdcf03187
dsa_R_ESP_32_1_5390:u32 = 0xffaf016c:u32
dsa_R_ECX_32_1_5391:u32 =
  pad:u32(dsa_mem_ffaf0183_1_5383:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf0182_1_5382:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf0181_1_5381:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf0180_1_5380:u8)))
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0xdd01cca0, 0, u32, wr
  @context "R_ECX_32" = 0x41414141, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_5392:u32 = 0xdd01cca0:u32
dsa_R_EAX_32_1_5393:u32 = dsa_R_ECX_32_1_5391:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x41414141, -1, u32, rw
  @context "R_EDX_32" = 0xbebebebf, -1, u32, wr
  @context "R_EFLAGS" = 0x292, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_5394:bool = false
dsa_R_EBP_32_1_5395:u32 = 0xcccccccd:u32
dsa_R_AF_1_5396:bool = true
dsa_R_OF_1_5397:bool = false
dsa_R_SF_1_5398:bool = true
dsa_R_DF_1_5399:bool = false
dsa_R_CF_1_5400:bool = false
dsa_R_EFLAGS_1_5401:u32 = 0x292:u32
dsa_R_PF_1_5402:bool = false
dsa_T_t_1_5403:u64 =
  pad:u64(dsa_R_EAX_32_1_5393:u32) * pad:u64(dsa_R_EBP_32_1_5395:u32)
dsa_R_EAX_32_1_5404:u32 = extract:31:0:[dsa_T_t_1_5403:u64]
dsa_R_EDX_32_1_5405:u32 = extract:63:32:[dsa_T_t_1_5403:u64]
dsa_R_OF_1_5406:bool = extract:63:32:[dsa_T_t_1_5403:u64] <> 0:u32
dsa_R_CF_1_5407:bool = extract:63:32:[dsa_T_t_1_5403:u64] <> 0:u32
dsa_R_SF_1_5408:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_5409:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_5410:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_5411:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x34343434, -1, u32, rw
  @context "R_EFLAGS" = 0xa03, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_5412:bool = false
dsa_T_origDEST_1_5413:u32 = dsa_R_EDX_32_1_5405:u32
dsa_T_origCOUNT_1_5414:u32 = 3:u32
dsa_R_EDX_32_1_5415:u32 = dsa_R_EDX_32_1_5405:u32 >> 3:u32
dsa_R_CF_1_5416:bool =
  if dsa_T_origCOUNT_1_5414:u32 == 0:u32 then dsa_R_CF_1_5407:bool else
  high:bool(dsa_T_origDEST_1_5413:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_5414:u32)
dsa_R_OF_1_5417:bool =
  if dsa_T_origCOUNT_1_5414:u32 == 0:u32 then dsa_R_OF_1_5406:bool else
  if dsa_T_origCOUNT_1_5414:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_5413:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_5418:bool =
  if dsa_T_origCOUNT_1_5414:u32 == 0:u32 then dsa_R_SF_1_5408:bool else
  high:bool(dsa_R_EDX_32_1_5415:u32)
dsa_R_ZF_1_5419:bool =
  if dsa_T_origCOUNT_1_5414:u32 == 0:u32 then dsa_R_ZF_1_5409:bool else
  0:u32 == dsa_R_EDX_32_1_5415:u32
dsa_R_PF_3_5422:bool =
  if dsa_T_origCOUNT_1_5414:u32 == 0:u32 then dsa_R_PF_1_5411:bool else
  ~low:bool(let dsa_T_acc_1_5420:u32 :=
                                         dsa_R_EDX_32_1_5415:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_5415:u32 in
            let dsa_T_acc_2_5421:u32 :=
                                         dsa_T_acc_1_5420:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5420:u32 in
            dsa_T_acc_2_5421:u32 >> 1:u32 ^ dsa_T_acc_2_5421:u32)
dsa_R_AF_1_5423:bool =
  if dsa_T_origCOUNT_1_5414:u32 == 0:u32 then dsa_R_AF_1_5410:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0xd0d0d0d, -1, u32, wr
  @context "R_EDX_32" = 0x6868686, -1, u32, rd
  @context "R_EDX_32" = 0x6868686, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_5424:u32 =
  dsa_R_EDX_32_1_5415:u32 + (dsa_R_EDX_32_1_5415:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x20a0a09e, -1, u32, rw
  @context "R_EAX_32" = 0x20a0a09e, -1, u32, rd
  @context "R_EFLAGS" = 0x203, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_5425:bool = false
dsa_T_t1_1_5426:u32 = dsa_R_EAX_32_1_5424:u32
dsa_T_t2_1_5427:u32 = dsa_R_EAX_32_1_5424:u32
dsa_R_EAX_32_1_5428:u32 = dsa_R_EAX_32_1_5424:u32 + dsa_T_t2_1_5427:u32
dsa_R_CF_1_5429:bool = dsa_R_EAX_32_1_5428:u32 < dsa_T_t1_1_5426:u32
dsa_R_OF_1_5430:bool =
  high:bool((dsa_T_t1_1_5426:u32 ^ ~dsa_T_t2_1_5427:u32) &
            (dsa_T_t1_1_5426:u32 ^ dsa_R_EAX_32_1_5428:u32))
dsa_R_AF_1_5431:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_5428:u32 ^ dsa_T_t1_1_5426:u32 ^ dsa_T_t2_1_5427:u32))
dsa_R_PF_3_5434:bool =
  ~low:bool(let dsa_T_acc_1_5432:u32 :=
                                         dsa_R_EAX_32_1_5428:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_5428:u32 in
            let dsa_T_acc_2_5433:u32 :=
                                         dsa_T_acc_1_5432:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5432:u32 in
            dsa_T_acc_2_5433:u32 >> 1:u32 ^ dsa_T_acc_2_5433:u32)
dsa_R_SF_1_5435:bool = high:bool(dsa_R_EAX_32_1_5428:u32)
dsa_R_ZF_1_5436:bool = 0:u32 == dsa_R_EAX_32_1_5428:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x41414141, -1, u32, rw
  @context "R_EAX_32" = 0x4141413c, -1, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_5437:bool = false
dsa_T_t_1_5438:u32 = dsa_R_ECX_32_1_5391:u32
dsa_R_ECX_32_1_5439:u32 = dsa_R_ECX_32_1_5391:u32 - dsa_R_EAX_32_1_5428:u32
dsa_R_CF_1_5440:bool = dsa_T_t_1_5438:u32 < dsa_R_EAX_32_1_5428:u32
dsa_R_OF_1_5441:bool =
  high:bool((dsa_T_t_1_5438:u32 ^ dsa_R_EAX_32_1_5428:u32) &
            (dsa_T_t_1_5438:u32 ^ dsa_R_ECX_32_1_5439:u32))
dsa_R_AF_1_5442:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_5439:u32 ^ dsa_T_t_1_5438:u32 ^ dsa_R_EAX_32_1_5428:u32))
dsa_R_PF_3_5445:bool =
  ~low:bool(let dsa_T_acc_1_5443:u32 :=
                                         dsa_R_ECX_32_1_5439:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_5439:u32 in
            let dsa_T_acc_2_5444:u32 :=
                                         dsa_T_acc_1_5443:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5443:u32 in
            dsa_T_acc_2_5444:u32 >> 1:u32 ^ dsa_T_acc_2_5444:u32)
dsa_R_SF_1_5446:bool = high:bool(dsa_R_ECX_32_1_5439:u32)
dsa_R_ZF_1_5447:bool = 0:u32 == dsa_R_ECX_32_1_5439:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x6868686, -1, u32, rd
  @context "R_EDX_32" = 0x6868686, -1, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_5448:bool = false
dsa_T_t_1_5449:u32 = dsa_R_EDX_32_1_5415:u32 & dsa_R_EDX_32_1_5415:u32
dsa_R_OF_1_5450:bool = false
dsa_R_CF_1_5451:bool = false
dsa_R_AF_1_5452:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_5455:bool =
  ~low:bool(let dsa_T_acc_1_5453:u32 :=
                                         dsa_T_t_1_5449:u32 >> 4:u32 ^
                                         dsa_T_t_1_5449:u32 in
            let dsa_T_acc_2_5454:u32 :=
                                         dsa_T_acc_1_5453:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5453:u32 in
            dsa_T_acc_2_5454:u32 >> 1:u32 ^ dsa_T_acc_2_5454:u32)
dsa_R_SF_1_5456:bool = high:bool(dsa_T_t_1_5449:u32)
dsa_R_ZF_1_5457:bool = 0:u32 == dsa_T_t_1_5449:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x4141413c, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x5, -1, u32, rd
  @context "mem32[0xdd01cc65]" = 0x35, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc65_1_5458:u8 = low:u8(0x35:u8)
dsa_R_EDI_32_1_5459:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_5460:u32 = pad:u32(pad:u8(dsa_mem_dd01cc65_1_5458:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x5, -1, u32, wr
  @context "R_EDX_32" = 0x6868686, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_5461:u32 = dsa_R_EDX_32_1_5415:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf067f, 0, u32, rd
  @context "R_EAX_32" = 0x35, -1, u32, rd
  @context "mem32[0xffaf067f]" = 0x35, -1, u8, wr
label pc_0xdcf03221
dsa_R_ESI_32_1_5462:u32 = 0xffaf067f:u32
dsa_mem_ffaf067f_1_5463:u8 = low:u8(low:u8(dsa_R_EAX_32_1_5460:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_5464:bool = false
dsa_R_EIP_1_5465:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_5457:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp139"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x35, -1, u32, wr
  @context "R_ECX_32" = 0x6868686, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_5466:u32 = dsa_R_ECX_32_1_5461:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf067f, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_5467:u32 = 0xffaf067f:u32
dsa_R_DF_1_5468:bool = false
dsa_T_t_1_5469:u32 = dsa_R_ESI_32_1_5467:u32
dsa_R_ESI_32_1_5470:u32 = dsa_R_ESI_32_1_5467:u32 - 1:u32
dsa_R_CF_1_5471:bool = dsa_T_t_1_5469:u32 < 1:u32
dsa_R_OF_1_5472:bool =
  high:bool((dsa_T_t_1_5469:u32 ^ 1:u32) &
            (dsa_T_t_1_5469:u32 ^ dsa_R_ESI_32_1_5470:u32))
dsa_R_AF_1_5473:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_5470:u32 ^ dsa_T_t_1_5469:u32 ^ 1:u32))
dsa_R_PF_3_5476:bool =
  ~low:bool(let dsa_T_acc_1_5474:u32 :=
                                         dsa_R_ESI_32_1_5470:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_5470:u32 in
            let dsa_T_acc_2_5475:u32 :=
                                         dsa_T_acc_1_5474:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5474:u32 in
            dsa_T_acc_2_5475:u32 >> 1:u32 ^ dsa_T_acc_2_5475:u32)
dsa_R_SF_1_5477:bool = high:bool(dsa_R_ESI_32_1_5470:u32)
dsa_R_ZF_1_5478:bool = 0:u32 == dsa_R_ESI_32_1_5470:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x6868686, -1, u32, rw
  @context "R_EDX_32" = 0x6868686, -1, u32, wr
  @context "R_EFLAGS" = 0x286, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_5479:bool = false
dsa_R_EBP_32_1_5480:u32 = 0xcccccccd:u32
dsa_R_AF_1_5481:bool = false
dsa_R_OF_1_5482:bool = false
dsa_R_SF_1_5483:bool = true
dsa_R_DF_1_5484:bool = false
dsa_R_CF_1_5485:bool = false
dsa_R_EFLAGS_1_5486:u32 = 0x286:u32
dsa_R_PF_1_5487:bool = true
dsa_T_t_1_5488:u64 =
  pad:u64(dsa_R_EAX_32_1_5466:u32) * pad:u64(dsa_R_EBP_32_1_5480:u32)
dsa_R_EAX_32_1_5489:u32 = extract:31:0:[dsa_T_t_1_5488:u64]
dsa_R_EDX_32_1_5490:u32 = extract:63:32:[dsa_T_t_1_5488:u64]
dsa_R_OF_1_5491:bool = extract:63:32:[dsa_T_t_1_5488:u64] <> 0:u32
dsa_R_CF_1_5492:bool = extract:63:32:[dsa_T_t_1_5488:u64] <> 0:u32
dsa_R_SF_1_5493:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_5494:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_5495:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_5496:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x5386b9e, -1, u32, rw
  @context "R_EFLAGS" = 0xa07, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_5497:bool = false
dsa_T_origDEST_1_5498:u32 = dsa_R_EDX_32_1_5490:u32
dsa_T_origCOUNT_1_5499:u32 = 3:u32
dsa_R_EDX_32_1_5500:u32 = dsa_R_EDX_32_1_5490:u32 >> 3:u32
dsa_R_CF_1_5501:bool =
  if dsa_T_origCOUNT_1_5499:u32 == 0:u32 then dsa_R_CF_1_5492:bool else
  high:bool(dsa_T_origDEST_1_5498:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_5499:u32)
dsa_R_OF_1_5502:bool =
  if dsa_T_origCOUNT_1_5499:u32 == 0:u32 then dsa_R_OF_1_5491:bool else
  if dsa_T_origCOUNT_1_5499:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_5498:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_5503:bool =
  if dsa_T_origCOUNT_1_5499:u32 == 0:u32 then dsa_R_SF_1_5493:bool else
  high:bool(dsa_R_EDX_32_1_5500:u32)
dsa_R_ZF_1_5504:bool =
  if dsa_T_origCOUNT_1_5499:u32 == 0:u32 then dsa_R_ZF_1_5494:bool else
  0:u32 == dsa_R_EDX_32_1_5500:u32
dsa_R_PF_3_5507:bool =
  if dsa_T_origCOUNT_1_5499:u32 == 0:u32 then dsa_R_PF_1_5496:bool else
  ~low:bool(let dsa_T_acc_1_5505:u32 :=
                                         dsa_R_EDX_32_1_5500:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_5500:u32 in
            let dsa_T_acc_2_5506:u32 :=
                                         dsa_T_acc_1_5505:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5505:u32 in
            dsa_T_acc_2_5506:u32 >> 1:u32 ^ dsa_T_acc_2_5506:u32)
dsa_R_AF_1_5508:bool =
  if dsa_T_origCOUNT_1_5499:u32 == 0:u32 then dsa_R_AF_1_5495:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x67b4814e, -1, u32, wr
  @context "R_EDX_32" = 0xa70d73, -1, u32, rd
  @context "R_EDX_32" = 0xa70d73, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_5509:u32 =
  dsa_R_EDX_32_1_5500:u32 + (dsa_R_EDX_32_1_5500:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x343433f, -1, u32, rw
  @context "R_EAX_32" = 0x343433f, -1, u32, rd
  @context "R_EFLAGS" = 0x203, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_5510:bool = false
dsa_T_t1_1_5511:u32 = dsa_R_EAX_32_1_5509:u32
dsa_T_t2_1_5512:u32 = dsa_R_EAX_32_1_5509:u32
dsa_R_EAX_32_1_5513:u32 = dsa_R_EAX_32_1_5509:u32 + dsa_T_t2_1_5512:u32
dsa_R_CF_1_5514:bool = dsa_R_EAX_32_1_5513:u32 < dsa_T_t1_1_5511:u32
dsa_R_OF_1_5515:bool =
  high:bool((dsa_T_t1_1_5511:u32 ^ ~dsa_T_t2_1_5512:u32) &
            (dsa_T_t1_1_5511:u32 ^ dsa_R_EAX_32_1_5513:u32))
dsa_R_AF_1_5516:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_5513:u32 ^ dsa_T_t1_1_5511:u32 ^ dsa_T_t2_1_5512:u32))
dsa_R_PF_3_5519:bool =
  ~low:bool(let dsa_T_acc_1_5517:u32 :=
                                         dsa_R_EAX_32_1_5513:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_5513:u32 in
            let dsa_T_acc_2_5518:u32 :=
                                         dsa_T_acc_1_5517:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5517:u32 in
            dsa_T_acc_2_5518:u32 >> 1:u32 ^ dsa_T_acc_2_5518:u32)
dsa_R_SF_1_5520:bool = high:bool(dsa_R_EAX_32_1_5513:u32)
dsa_R_ZF_1_5521:bool = 0:u32 == dsa_R_EAX_32_1_5513:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x6868686, -1, u32, rw
  @context "R_EAX_32" = 0x686867e, -1, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_5522:bool = false
dsa_T_t_1_5523:u32 = dsa_R_ECX_32_1_5461:u32
dsa_R_ECX_32_1_5524:u32 = dsa_R_ECX_32_1_5461:u32 - dsa_R_EAX_32_1_5513:u32
dsa_R_CF_1_5525:bool = dsa_T_t_1_5523:u32 < dsa_R_EAX_32_1_5513:u32
dsa_R_OF_1_5526:bool =
  high:bool((dsa_T_t_1_5523:u32 ^ dsa_R_EAX_32_1_5513:u32) &
            (dsa_T_t_1_5523:u32 ^ dsa_R_ECX_32_1_5524:u32))
dsa_R_AF_1_5527:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_5524:u32 ^ dsa_T_t_1_5523:u32 ^ dsa_R_EAX_32_1_5513:u32))
dsa_R_PF_3_5530:bool =
  ~low:bool(let dsa_T_acc_1_5528:u32 :=
                                         dsa_R_ECX_32_1_5524:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_5524:u32 in
            let dsa_T_acc_2_5529:u32 :=
                                         dsa_T_acc_1_5528:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5528:u32 in
            dsa_T_acc_2_5529:u32 >> 1:u32 ^ dsa_T_acc_2_5529:u32)
dsa_R_SF_1_5531:bool = high:bool(dsa_R_ECX_32_1_5524:u32)
dsa_R_ZF_1_5532:bool = 0:u32 == dsa_R_ECX_32_1_5524:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0xa70d73, -1, u32, rd
  @context "R_EDX_32" = 0xa70d73, -1, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_5533:bool = false
dsa_T_t_1_5534:u32 = dsa_R_EDX_32_1_5500:u32 & dsa_R_EDX_32_1_5500:u32
dsa_R_OF_1_5535:bool = false
dsa_R_CF_1_5536:bool = false
dsa_R_AF_1_5537:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_5540:bool =
  ~low:bool(let dsa_T_acc_1_5538:u32 :=
                                         dsa_T_t_1_5534:u32 >> 4:u32 ^
                                         dsa_T_t_1_5534:u32 in
            let dsa_T_acc_2_5539:u32 :=
                                         dsa_T_acc_1_5538:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5538:u32 in
            dsa_T_acc_2_5539:u32 >> 1:u32 ^ dsa_T_acc_2_5539:u32)
dsa_R_SF_1_5541:bool = high:bool(dsa_T_t_1_5534:u32)
dsa_R_ZF_1_5542:bool = 0:u32 == dsa_T_t_1_5534:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x686867e, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x8, -1, u32, rd
  @context "mem32[0xdd01cc68]" = 0x38, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc68_1_5543:u8 = low:u8(0x38:u8)
dsa_R_EDI_32_1_5544:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_5545:u32 = pad:u32(pad:u8(dsa_mem_dd01cc68_1_5543:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x8, -1, u32, wr
  @context "R_EDX_32" = 0xa70d73, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_5546:u32 = dsa_R_EDX_32_1_5500:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf067e, 0, u32, rd
  @context "R_EAX_32" = 0x38, -1, u32, rd
  @context "mem32[0xffaf067e]" = 0x38, -1, u8, wr
label pc_0xdcf03221
dsa_R_ESI_32_1_5547:u32 = 0xffaf067e:u32
dsa_mem_ffaf067e_1_5548:u8 = low:u8(low:u8(dsa_R_EAX_32_1_5545:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_5549:bool = false
dsa_R_EIP_1_5550:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_5542:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp140"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x38, -1, u32, wr
  @context "R_ECX_32" = 0xa70d73, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_5551:u32 = dsa_R_ECX_32_1_5546:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf067e, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_5552:u32 = 0xffaf067e:u32
dsa_R_DF_1_5553:bool = false
dsa_T_t_1_5554:u32 = dsa_R_ESI_32_1_5552:u32
dsa_R_ESI_32_1_5555:u32 = dsa_R_ESI_32_1_5552:u32 - 1:u32
dsa_R_CF_1_5556:bool = dsa_T_t_1_5554:u32 < 1:u32
dsa_R_OF_1_5557:bool =
  high:bool((dsa_T_t_1_5554:u32 ^ 1:u32) &
            (dsa_T_t_1_5554:u32 ^ dsa_R_ESI_32_1_5555:u32))
dsa_R_AF_1_5558:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_5555:u32 ^ dsa_T_t_1_5554:u32 ^ 1:u32))
dsa_R_PF_3_5561:bool =
  ~low:bool(let dsa_T_acc_1_5559:u32 :=
                                         dsa_R_ESI_32_1_5555:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_5555:u32 in
            let dsa_T_acc_2_5560:u32 :=
                                         dsa_T_acc_1_5559:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5559:u32 in
            dsa_T_acc_2_5560:u32 >> 1:u32 ^ dsa_T_acc_2_5560:u32)
dsa_R_SF_1_5562:bool = high:bool(dsa_R_ESI_32_1_5555:u32)
dsa_R_ZF_1_5563:bool = 0:u32 == dsa_R_ESI_32_1_5555:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0xa70d73, -1, u32, rw
  @context "R_EDX_32" = 0xa70d73, -1, u32, wr
  @context "R_EFLAGS" = 0x286, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_5564:bool = false
dsa_R_EBP_32_1_5565:u32 = 0xcccccccd:u32
dsa_R_AF_1_5566:bool = false
dsa_R_OF_1_5567:bool = false
dsa_R_SF_1_5568:bool = true
dsa_R_DF_1_5569:bool = false
dsa_R_CF_1_5570:bool = false
dsa_R_EFLAGS_1_5571:u32 = 0x286:u32
dsa_R_PF_1_5572:bool = true
dsa_T_t_1_5573:u64 =
  pad:u64(dsa_R_EAX_32_1_5551:u32) * pad:u64(dsa_R_EBP_32_1_5565:u32)
dsa_R_EAX_32_1_5574:u32 = extract:31:0:[dsa_T_t_1_5573:u64]
dsa_R_EDX_32_1_5575:u32 = extract:63:32:[dsa_T_t_1_5573:u64]
dsa_R_OF_1_5576:bool = extract:63:32:[dsa_T_t_1_5573:u64] <> 0:u32
dsa_R_CF_1_5577:bool = extract:63:32:[dsa_T_t_1_5573:u64] <> 0:u32
dsa_R_SF_1_5578:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_5579:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_5580:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_5581:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x85a45c, -1, u32, rw
  @context "R_EFLAGS" = 0xa07, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_5582:bool = false
dsa_T_origDEST_1_5583:u32 = dsa_R_EDX_32_1_5575:u32
dsa_T_origCOUNT_1_5584:u32 = 3:u32
dsa_R_EDX_32_1_5585:u32 = dsa_R_EDX_32_1_5575:u32 >> 3:u32
dsa_R_CF_1_5586:bool =
  if dsa_T_origCOUNT_1_5584:u32 == 0:u32 then dsa_R_CF_1_5577:bool else
  high:bool(dsa_T_origDEST_1_5583:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_5584:u32)
dsa_R_OF_1_5587:bool =
  if dsa_T_origCOUNT_1_5584:u32 == 0:u32 then dsa_R_OF_1_5576:bool else
  if dsa_T_origCOUNT_1_5584:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_5583:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_5588:bool =
  if dsa_T_origCOUNT_1_5584:u32 == 0:u32 then dsa_R_SF_1_5578:bool else
  high:bool(dsa_R_EDX_32_1_5585:u32)
dsa_R_ZF_1_5589:bool =
  if dsa_T_origCOUNT_1_5584:u32 == 0:u32 then dsa_R_ZF_1_5579:bool else
  0:u32 == dsa_R_EDX_32_1_5585:u32
dsa_R_PF_3_5592:bool =
  if dsa_T_origCOUNT_1_5584:u32 == 0:u32 then dsa_R_PF_1_5581:bool else
  ~low:bool(let dsa_T_acc_1_5590:u32 :=
                                         dsa_R_EDX_32_1_5585:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_5585:u32 in
            let dsa_T_acc_2_5591:u32 :=
                                         dsa_T_acc_1_5590:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5590:u32 in
            dsa_T_acc_2_5591:u32 >> 1:u32 ^ dsa_T_acc_2_5591:u32)
dsa_R_AF_1_5593:bool =
  if dsa_T_origCOUNT_1_5584:u32 == 0:u32 then dsa_R_AF_1_5580:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x216917, -1, u32, wr
  @context "R_EDX_32" = 0x10b48b, -1, u32, rd
  @context "R_EDX_32" = 0x10b48b, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_5594:u32 =
  dsa_R_EDX_32_1_5585:u32 + (dsa_R_EDX_32_1_5585:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x5386b7, -1, u32, rw
  @context "R_EAX_32" = 0x5386b7, -1, u32, rd
  @context "R_EFLAGS" = 0x207, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_5595:bool = false
dsa_T_t1_1_5596:u32 = dsa_R_EAX_32_1_5594:u32
dsa_T_t2_1_5597:u32 = dsa_R_EAX_32_1_5594:u32
dsa_R_EAX_32_1_5598:u32 = dsa_R_EAX_32_1_5594:u32 + dsa_T_t2_1_5597:u32
dsa_R_CF_1_5599:bool = dsa_R_EAX_32_1_5598:u32 < dsa_T_t1_1_5596:u32
dsa_R_OF_1_5600:bool =
  high:bool((dsa_T_t1_1_5596:u32 ^ ~dsa_T_t2_1_5597:u32) &
            (dsa_T_t1_1_5596:u32 ^ dsa_R_EAX_32_1_5598:u32))
dsa_R_AF_1_5601:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_5598:u32 ^ dsa_T_t1_1_5596:u32 ^ dsa_T_t2_1_5597:u32))
dsa_R_PF_3_5604:bool =
  ~low:bool(let dsa_T_acc_1_5602:u32 :=
                                         dsa_R_EAX_32_1_5598:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_5598:u32 in
            let dsa_T_acc_2_5603:u32 :=
                                         dsa_T_acc_1_5602:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5602:u32 in
            dsa_T_acc_2_5603:u32 >> 1:u32 ^ dsa_T_acc_2_5603:u32)
dsa_R_SF_1_5605:bool = high:bool(dsa_R_EAX_32_1_5598:u32)
dsa_R_ZF_1_5606:bool = 0:u32 == dsa_R_EAX_32_1_5598:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0xa70d73, -1, u32, rw
  @context "R_EAX_32" = 0xa70d6e, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_5607:bool = false
dsa_T_t_1_5608:u32 = dsa_R_ECX_32_1_5546:u32
dsa_R_ECX_32_1_5609:u32 = dsa_R_ECX_32_1_5546:u32 - dsa_R_EAX_32_1_5598:u32
dsa_R_CF_1_5610:bool = dsa_T_t_1_5608:u32 < dsa_R_EAX_32_1_5598:u32
dsa_R_OF_1_5611:bool =
  high:bool((dsa_T_t_1_5608:u32 ^ dsa_R_EAX_32_1_5598:u32) &
            (dsa_T_t_1_5608:u32 ^ dsa_R_ECX_32_1_5609:u32))
dsa_R_AF_1_5612:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_5609:u32 ^ dsa_T_t_1_5608:u32 ^ dsa_R_EAX_32_1_5598:u32))
dsa_R_PF_3_5615:bool =
  ~low:bool(let dsa_T_acc_1_5613:u32 :=
                                         dsa_R_ECX_32_1_5609:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_5609:u32 in
            let dsa_T_acc_2_5614:u32 :=
                                         dsa_T_acc_1_5613:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5613:u32 in
            dsa_T_acc_2_5614:u32 >> 1:u32 ^ dsa_T_acc_2_5614:u32)
dsa_R_SF_1_5616:bool = high:bool(dsa_R_ECX_32_1_5609:u32)
dsa_R_ZF_1_5617:bool = 0:u32 == dsa_R_ECX_32_1_5609:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x10b48b, -1, u32, rd
  @context "R_EDX_32" = 0x10b48b, -1, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_5618:bool = false
dsa_T_t_1_5619:u32 = dsa_R_EDX_32_1_5585:u32 & dsa_R_EDX_32_1_5585:u32
dsa_R_OF_1_5620:bool = false
dsa_R_CF_1_5621:bool = false
dsa_R_AF_1_5622:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_5625:bool =
  ~low:bool(let dsa_T_acc_1_5623:u32 :=
                                         dsa_T_t_1_5619:u32 >> 4:u32 ^
                                         dsa_T_t_1_5619:u32 in
            let dsa_T_acc_2_5624:u32 :=
                                         dsa_T_acc_1_5623:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5623:u32 in
            dsa_T_acc_2_5624:u32 >> 1:u32 ^ dsa_T_acc_2_5624:u32)
dsa_R_SF_1_5626:bool = high:bool(dsa_T_t_1_5619:u32)
dsa_R_ZF_1_5627:bool = 0:u32 == dsa_T_t_1_5619:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0xa70d6e, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x5, -1, u32, rd
  @context "mem32[0xdd01cc65]" = 0x35, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc65_1_5628:u8 = low:u8(0x35:u8)
dsa_R_EDI_32_1_5629:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_5630:u32 = pad:u32(pad:u8(dsa_mem_dd01cc65_1_5628:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x5, -1, u32, wr
  @context "R_EDX_32" = 0x10b48b, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_5631:u32 = dsa_R_EDX_32_1_5585:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf067d, 0, u32, rd
  @context "R_EAX_32" = 0x35, -1, u32, rd
  @context "mem32[0xffaf067d]" = 0x35, -1, u8, wr
label pc_0xdcf03221
dsa_R_ESI_32_1_5632:u32 = 0xffaf067d:u32
dsa_mem_ffaf067d_1_5633:u8 = low:u8(low:u8(dsa_R_EAX_32_1_5630:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_5634:bool = false
dsa_R_EIP_1_5635:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_5627:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp141"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x35, -1, u32, wr
  @context "R_ECX_32" = 0x10b48b, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_5636:u32 = dsa_R_ECX_32_1_5631:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf067d, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_5637:u32 = 0xffaf067d:u32
dsa_R_DF_1_5638:bool = false
dsa_T_t_1_5639:u32 = dsa_R_ESI_32_1_5637:u32
dsa_R_ESI_32_1_5640:u32 = dsa_R_ESI_32_1_5637:u32 - 1:u32
dsa_R_CF_1_5641:bool = dsa_T_t_1_5639:u32 < 1:u32
dsa_R_OF_1_5642:bool =
  high:bool((dsa_T_t_1_5639:u32 ^ 1:u32) &
            (dsa_T_t_1_5639:u32 ^ dsa_R_ESI_32_1_5640:u32))
dsa_R_AF_1_5643:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_5640:u32 ^ dsa_T_t_1_5639:u32 ^ 1:u32))
dsa_R_PF_3_5646:bool =
  ~low:bool(let dsa_T_acc_1_5644:u32 :=
                                         dsa_R_ESI_32_1_5640:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_5640:u32 in
            let dsa_T_acc_2_5645:u32 :=
                                         dsa_T_acc_1_5644:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5644:u32 in
            dsa_T_acc_2_5645:u32 >> 1:u32 ^ dsa_T_acc_2_5645:u32)
dsa_R_SF_1_5647:bool = high:bool(dsa_R_ESI_32_1_5640:u32)
dsa_R_ZF_1_5648:bool = 0:u32 == dsa_R_ESI_32_1_5640:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x10b48b, -1, u32, rw
  @context "R_EDX_32" = 0x10b48b, -1, u32, wr
  @context "R_EFLAGS" = 0x282, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_5649:bool = false
dsa_R_EBP_32_1_5650:u32 = 0xcccccccd:u32
dsa_R_AF_1_5651:bool = false
dsa_R_OF_1_5652:bool = false
dsa_R_SF_1_5653:bool = true
dsa_R_DF_1_5654:bool = false
dsa_R_CF_1_5655:bool = false
dsa_R_EFLAGS_1_5656:u32 = 0x282:u32
dsa_R_PF_1_5657:bool = false
dsa_T_t_1_5658:u64 =
  pad:u64(dsa_R_EAX_32_1_5636:u32) * pad:u64(dsa_R_EBP_32_1_5650:u32)
dsa_R_EAX_32_1_5659:u32 = extract:31:0:[dsa_T_t_1_5658:u64]
dsa_R_EDX_32_1_5660:u32 = extract:63:32:[dsa_T_t_1_5658:u64]
dsa_R_OF_1_5661:bool = extract:63:32:[dsa_T_t_1_5658:u64] <> 0:u32
dsa_R_CF_1_5662:bool = extract:63:32:[dsa_T_t_1_5658:u64] <> 0:u32
dsa_R_SF_1_5663:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_5664:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_5665:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_5666:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0xd5d3c, -1, u32, rw
  @context "R_EFLAGS" = 0xa03, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_5667:bool = false
dsa_T_origDEST_1_5668:u32 = dsa_R_EDX_32_1_5660:u32
dsa_T_origCOUNT_1_5669:u32 = 3:u32
dsa_R_EDX_32_1_5670:u32 = dsa_R_EDX_32_1_5660:u32 >> 3:u32
dsa_R_CF_1_5671:bool =
  if dsa_T_origCOUNT_1_5669:u32 == 0:u32 then dsa_R_CF_1_5662:bool else
  high:bool(dsa_T_origDEST_1_5668:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_5669:u32)
dsa_R_OF_1_5672:bool =
  if dsa_T_origCOUNT_1_5669:u32 == 0:u32 then dsa_R_OF_1_5661:bool else
  if dsa_T_origCOUNT_1_5669:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_5668:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_5673:bool =
  if dsa_T_origCOUNT_1_5669:u32 == 0:u32 then dsa_R_SF_1_5663:bool else
  high:bool(dsa_R_EDX_32_1_5670:u32)
dsa_R_ZF_1_5674:bool =
  if dsa_T_origCOUNT_1_5669:u32 == 0:u32 then dsa_R_ZF_1_5664:bool else
  0:u32 == dsa_R_EDX_32_1_5670:u32
dsa_R_PF_3_5677:bool =
  if dsa_T_origCOUNT_1_5669:u32 == 0:u32 then dsa_R_PF_1_5666:bool else
  ~low:bool(let dsa_T_acc_1_5675:u32 :=
                                         dsa_R_EDX_32_1_5670:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_5670:u32 in
            let dsa_T_acc_2_5676:u32 :=
                                         dsa_T_acc_1_5675:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5675:u32 in
            dsa_T_acc_2_5676:u32 >> 1:u32 ^ dsa_T_acc_2_5676:u32)
dsa_R_AF_1_5678:bool =
  if dsa_T_origCOUNT_1_5669:u32 == 0:u32 then dsa_R_AF_1_5665:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x3574f, -1, u32, wr
  @context "R_EDX_32" = 0x1aba7, -1, u32, rd
  @context "R_EDX_32" = 0x1aba7, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_5679:u32 =
  dsa_R_EDX_32_1_5670:u32 + (dsa_R_EDX_32_1_5670:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x85a43, -1, u32, rw
  @context "R_EAX_32" = 0x85a43, -1, u32, rd
  @context "R_EFLAGS" = 0x203, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_5680:bool = false
dsa_T_t1_1_5681:u32 = dsa_R_EAX_32_1_5679:u32
dsa_T_t2_1_5682:u32 = dsa_R_EAX_32_1_5679:u32
dsa_R_EAX_32_1_5683:u32 = dsa_R_EAX_32_1_5679:u32 + dsa_T_t2_1_5682:u32
dsa_R_CF_1_5684:bool = dsa_R_EAX_32_1_5683:u32 < dsa_T_t1_1_5681:u32
dsa_R_OF_1_5685:bool =
  high:bool((dsa_T_t1_1_5681:u32 ^ ~dsa_T_t2_1_5682:u32) &
            (dsa_T_t1_1_5681:u32 ^ dsa_R_EAX_32_1_5683:u32))
dsa_R_AF_1_5686:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_5683:u32 ^ dsa_T_t1_1_5681:u32 ^ dsa_T_t2_1_5682:u32))
dsa_R_PF_3_5689:bool =
  ~low:bool(let dsa_T_acc_1_5687:u32 :=
                                         dsa_R_EAX_32_1_5683:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_5683:u32 in
            let dsa_T_acc_2_5688:u32 :=
                                         dsa_T_acc_1_5687:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5687:u32 in
            dsa_T_acc_2_5688:u32 >> 1:u32 ^ dsa_T_acc_2_5688:u32)
dsa_R_SF_1_5690:bool = high:bool(dsa_R_EAX_32_1_5683:u32)
dsa_R_ZF_1_5691:bool = 0:u32 == dsa_R_EAX_32_1_5683:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x10b48b, -1, u32, rw
  @context "R_EAX_32" = 0x10b486, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_5692:bool = false
dsa_T_t_1_5693:u32 = dsa_R_ECX_32_1_5631:u32
dsa_R_ECX_32_1_5694:u32 = dsa_R_ECX_32_1_5631:u32 - dsa_R_EAX_32_1_5683:u32
dsa_R_CF_1_5695:bool = dsa_T_t_1_5693:u32 < dsa_R_EAX_32_1_5683:u32
dsa_R_OF_1_5696:bool =
  high:bool((dsa_T_t_1_5693:u32 ^ dsa_R_EAX_32_1_5683:u32) &
            (dsa_T_t_1_5693:u32 ^ dsa_R_ECX_32_1_5694:u32))
dsa_R_AF_1_5697:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_5694:u32 ^ dsa_T_t_1_5693:u32 ^ dsa_R_EAX_32_1_5683:u32))
dsa_R_PF_3_5700:bool =
  ~low:bool(let dsa_T_acc_1_5698:u32 :=
                                         dsa_R_ECX_32_1_5694:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_5694:u32 in
            let dsa_T_acc_2_5699:u32 :=
                                         dsa_T_acc_1_5698:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5698:u32 in
            dsa_T_acc_2_5699:u32 >> 1:u32 ^ dsa_T_acc_2_5699:u32)
dsa_R_SF_1_5701:bool = high:bool(dsa_R_ECX_32_1_5694:u32)
dsa_R_ZF_1_5702:bool = 0:u32 == dsa_R_ECX_32_1_5694:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x1aba7, -1, u32, rd
  @context "R_EDX_32" = 0x1aba7, -1, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_5703:bool = false
dsa_T_t_1_5704:u32 = dsa_R_EDX_32_1_5670:u32 & dsa_R_EDX_32_1_5670:u32
dsa_R_OF_1_5705:bool = false
dsa_R_CF_1_5706:bool = false
dsa_R_AF_1_5707:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_5710:bool =
  ~low:bool(let dsa_T_acc_1_5708:u32 :=
                                         dsa_T_t_1_5704:u32 >> 4:u32 ^
                                         dsa_T_t_1_5704:u32 in
            let dsa_T_acc_2_5709:u32 :=
                                         dsa_T_acc_1_5708:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5708:u32 in
            dsa_T_acc_2_5709:u32 >> 1:u32 ^ dsa_T_acc_2_5709:u32)
dsa_R_SF_1_5711:bool = high:bool(dsa_T_t_1_5704:u32)
dsa_R_ZF_1_5712:bool = 0:u32 == dsa_T_t_1_5704:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x10b486, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x5, -1, u32, rd
  @context "mem32[0xdd01cc65]" = 0x35, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc65_1_5713:u8 = low:u8(0x35:u8)
dsa_R_EDI_32_1_5714:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_5715:u32 = pad:u32(pad:u8(dsa_mem_dd01cc65_1_5713:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x5, -1, u32, wr
  @context "R_EDX_32" = 0x1aba7, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_5716:u32 = dsa_R_EDX_32_1_5670:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf067c, 0, u32, rd
  @context "R_EAX_32" = 0x35, -1, u32, rd
  @context "mem32[0xffaf067c]" = 0x35, -1, u8, wr
label pc_0xdcf03221
dsa_R_ESI_32_1_5717:u32 = 0xffaf067c:u32
dsa_mem_ffaf067c_1_5718:u8 = low:u8(low:u8(dsa_R_EAX_32_1_5715:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_5719:bool = false
dsa_R_EIP_1_5720:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_5712:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp142"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x35, -1, u32, wr
  @context "R_ECX_32" = 0x1aba7, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_5721:u32 = dsa_R_ECX_32_1_5716:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf067c, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_5722:u32 = 0xffaf067c:u32
dsa_R_DF_1_5723:bool = false
dsa_T_t_1_5724:u32 = dsa_R_ESI_32_1_5722:u32
dsa_R_ESI_32_1_5725:u32 = dsa_R_ESI_32_1_5722:u32 - 1:u32
dsa_R_CF_1_5726:bool = dsa_T_t_1_5724:u32 < 1:u32
dsa_R_OF_1_5727:bool =
  high:bool((dsa_T_t_1_5724:u32 ^ 1:u32) &
            (dsa_T_t_1_5724:u32 ^ dsa_R_ESI_32_1_5725:u32))
dsa_R_AF_1_5728:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_5725:u32 ^ dsa_T_t_1_5724:u32 ^ 1:u32))
dsa_R_PF_3_5731:bool =
  ~low:bool(let dsa_T_acc_1_5729:u32 :=
                                         dsa_R_ESI_32_1_5725:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_5725:u32 in
            let dsa_T_acc_2_5730:u32 :=
                                         dsa_T_acc_1_5729:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5729:u32 in
            dsa_T_acc_2_5730:u32 >> 1:u32 ^ dsa_T_acc_2_5730:u32)
dsa_R_SF_1_5732:bool = high:bool(dsa_R_ESI_32_1_5725:u32)
dsa_R_ZF_1_5733:bool = 0:u32 == dsa_R_ESI_32_1_5725:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x1aba7, -1, u32, rw
  @context "R_EDX_32" = 0x1aba7, -1, u32, wr
  @context "R_EFLAGS" = 0x286, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_5734:bool = false
dsa_R_EBP_32_1_5735:u32 = 0xcccccccd:u32
dsa_R_AF_1_5736:bool = false
dsa_R_OF_1_5737:bool = false
dsa_R_SF_1_5738:bool = true
dsa_R_DF_1_5739:bool = false
dsa_R_CF_1_5740:bool = false
dsa_R_EFLAGS_1_5741:u32 = 0x286:u32
dsa_R_PF_1_5742:bool = true
dsa_T_t_1_5743:u64 =
  pad:u64(dsa_R_EAX_32_1_5721:u32) * pad:u64(dsa_R_EBP_32_1_5735:u32)
dsa_R_EAX_32_1_5744:u32 = extract:31:0:[dsa_T_t_1_5743:u64]
dsa_R_EDX_32_1_5745:u32 = extract:63:32:[dsa_T_t_1_5743:u64]
dsa_R_OF_1_5746:bool = extract:63:32:[dsa_T_t_1_5743:u64] <> 0:u32
dsa_R_CF_1_5747:bool = extract:63:32:[dsa_T_t_1_5743:u64] <> 0:u32
dsa_R_SF_1_5748:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_5749:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_5750:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_5751:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x1561f, -1, u32, rw
  @context "R_EFLAGS" = 0xa07, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_5752:bool = false
dsa_T_origDEST_1_5753:u32 = dsa_R_EDX_32_1_5745:u32
dsa_T_origCOUNT_1_5754:u32 = 3:u32
dsa_R_EDX_32_1_5755:u32 = dsa_R_EDX_32_1_5745:u32 >> 3:u32
dsa_R_CF_1_5756:bool =
  if dsa_T_origCOUNT_1_5754:u32 == 0:u32 then dsa_R_CF_1_5747:bool else
  high:bool(dsa_T_origDEST_1_5753:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_5754:u32)
dsa_R_OF_1_5757:bool =
  if dsa_T_origCOUNT_1_5754:u32 == 0:u32 then dsa_R_OF_1_5746:bool else
  if dsa_T_origCOUNT_1_5754:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_5753:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_5758:bool =
  if dsa_T_origCOUNT_1_5754:u32 == 0:u32 then dsa_R_SF_1_5748:bool else
  high:bool(dsa_R_EDX_32_1_5755:u32)
dsa_R_ZF_1_5759:bool =
  if dsa_T_origCOUNT_1_5754:u32 == 0:u32 then dsa_R_ZF_1_5749:bool else
  0:u32 == dsa_R_EDX_32_1_5755:u32
dsa_R_PF_3_5762:bool =
  if dsa_T_origCOUNT_1_5754:u32 == 0:u32 then dsa_R_PF_1_5751:bool else
  ~low:bool(let dsa_T_acc_1_5760:u32 :=
                                         dsa_R_EDX_32_1_5755:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_5755:u32 in
            let dsa_T_acc_2_5761:u32 :=
                                         dsa_T_acc_1_5760:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5760:u32 in
            dsa_T_acc_2_5761:u32 >> 1:u32 ^ dsa_T_acc_2_5761:u32)
dsa_R_AF_1_5763:bool =
  if dsa_T_origCOUNT_1_5754:u32 == 0:u32 then dsa_R_AF_1_5750:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x333388bb, -1, u32, wr
  @context "R_EDX_32" = 0x2ac3, -1, u32, rd
  @context "R_EDX_32" = 0x2ac3, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_5764:u32 =
  dsa_R_EDX_32_1_5755:u32 + (dsa_R_EDX_32_1_5755:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0xd5cf, -1, u32, rw
  @context "R_EAX_32" = 0xd5cf, -1, u32, rd
  @context "R_EFLAGS" = 0x207, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_5765:bool = false
dsa_T_t1_1_5766:u32 = dsa_R_EAX_32_1_5764:u32
dsa_T_t2_1_5767:u32 = dsa_R_EAX_32_1_5764:u32
dsa_R_EAX_32_1_5768:u32 = dsa_R_EAX_32_1_5764:u32 + dsa_T_t2_1_5767:u32
dsa_R_CF_1_5769:bool = dsa_R_EAX_32_1_5768:u32 < dsa_T_t1_1_5766:u32
dsa_R_OF_1_5770:bool =
  high:bool((dsa_T_t1_1_5766:u32 ^ ~dsa_T_t2_1_5767:u32) &
            (dsa_T_t1_1_5766:u32 ^ dsa_R_EAX_32_1_5768:u32))
dsa_R_AF_1_5771:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_5768:u32 ^ dsa_T_t1_1_5766:u32 ^ dsa_T_t2_1_5767:u32))
dsa_R_PF_3_5774:bool =
  ~low:bool(let dsa_T_acc_1_5772:u32 :=
                                         dsa_R_EAX_32_1_5768:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_5768:u32 in
            let dsa_T_acc_2_5773:u32 :=
                                         dsa_T_acc_1_5772:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5772:u32 in
            dsa_T_acc_2_5773:u32 >> 1:u32 ^ dsa_T_acc_2_5773:u32)
dsa_R_SF_1_5775:bool = high:bool(dsa_R_EAX_32_1_5768:u32)
dsa_R_ZF_1_5776:bool = 0:u32 == dsa_R_EAX_32_1_5768:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x1aba7, -1, u32, rw
  @context "R_EAX_32" = 0x1ab9e, -1, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_5777:bool = false
dsa_T_t_1_5778:u32 = dsa_R_ECX_32_1_5716:u32
dsa_R_ECX_32_1_5779:u32 = dsa_R_ECX_32_1_5716:u32 - dsa_R_EAX_32_1_5768:u32
dsa_R_CF_1_5780:bool = dsa_T_t_1_5778:u32 < dsa_R_EAX_32_1_5768:u32
dsa_R_OF_1_5781:bool =
  high:bool((dsa_T_t_1_5778:u32 ^ dsa_R_EAX_32_1_5768:u32) &
            (dsa_T_t_1_5778:u32 ^ dsa_R_ECX_32_1_5779:u32))
dsa_R_AF_1_5782:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_5779:u32 ^ dsa_T_t_1_5778:u32 ^ dsa_R_EAX_32_1_5768:u32))
dsa_R_PF_3_5785:bool =
  ~low:bool(let dsa_T_acc_1_5783:u32 :=
                                         dsa_R_ECX_32_1_5779:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_5779:u32 in
            let dsa_T_acc_2_5784:u32 :=
                                         dsa_T_acc_1_5783:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5783:u32 in
            dsa_T_acc_2_5784:u32 >> 1:u32 ^ dsa_T_acc_2_5784:u32)
dsa_R_SF_1_5786:bool = high:bool(dsa_R_ECX_32_1_5779:u32)
dsa_R_ZF_1_5787:bool = 0:u32 == dsa_R_ECX_32_1_5779:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x2ac3, -1, u32, rd
  @context "R_EDX_32" = 0x2ac3, -1, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_5788:bool = false
dsa_T_t_1_5789:u32 = dsa_R_EDX_32_1_5755:u32 & dsa_R_EDX_32_1_5755:u32
dsa_R_OF_1_5790:bool = false
dsa_R_CF_1_5791:bool = false
dsa_R_AF_1_5792:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_5795:bool =
  ~low:bool(let dsa_T_acc_1_5793:u32 :=
                                         dsa_T_t_1_5789:u32 >> 4:u32 ^
                                         dsa_T_t_1_5789:u32 in
            let dsa_T_acc_2_5794:u32 :=
                                         dsa_T_acc_1_5793:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5793:u32 in
            dsa_T_acc_2_5794:u32 >> 1:u32 ^ dsa_T_acc_2_5794:u32)
dsa_R_SF_1_5796:bool = high:bool(dsa_T_t_1_5789:u32)
dsa_R_ZF_1_5797:bool = 0:u32 == dsa_T_t_1_5789:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x1ab9e, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x9, -1, u32, rd
  @context "mem32[0xdd01cc69]" = 0x39, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc69_1_5798:u8 = low:u8(0x39:u8)
dsa_R_EDI_32_1_5799:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_5800:u32 = pad:u32(pad:u8(dsa_mem_dd01cc69_1_5798:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x9, -1, u32, wr
  @context "R_EDX_32" = 0x2ac3, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_5801:u32 = dsa_R_EDX_32_1_5755:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf067b, 0, u32, rd
  @context "R_EAX_32" = 0x39, -1, u32, rd
  @context "mem32[0xffaf067b]" = 0x39, -1, u8, wr
label pc_0xdcf03221
dsa_R_ESI_32_1_5802:u32 = 0xffaf067b:u32
dsa_mem_ffaf067b_1_5803:u8 = low:u8(low:u8(dsa_R_EAX_32_1_5800:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_5804:bool = false
dsa_R_EIP_1_5805:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_5797:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp143"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x39, -1, u32, wr
  @context "R_ECX_32" = 0x2ac3, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_5806:u32 = dsa_R_ECX_32_1_5801:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf067b, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_5807:u32 = 0xffaf067b:u32
dsa_R_DF_1_5808:bool = false
dsa_T_t_1_5809:u32 = dsa_R_ESI_32_1_5807:u32
dsa_R_ESI_32_1_5810:u32 = dsa_R_ESI_32_1_5807:u32 - 1:u32
dsa_R_CF_1_5811:bool = dsa_T_t_1_5809:u32 < 1:u32
dsa_R_OF_1_5812:bool =
  high:bool((dsa_T_t_1_5809:u32 ^ 1:u32) &
            (dsa_T_t_1_5809:u32 ^ dsa_R_ESI_32_1_5810:u32))
dsa_R_AF_1_5813:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_5810:u32 ^ dsa_T_t_1_5809:u32 ^ 1:u32))
dsa_R_PF_3_5816:bool =
  ~low:bool(let dsa_T_acc_1_5814:u32 :=
                                         dsa_R_ESI_32_1_5810:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_5810:u32 in
            let dsa_T_acc_2_5815:u32 :=
                                         dsa_T_acc_1_5814:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5814:u32 in
            dsa_T_acc_2_5815:u32 >> 1:u32 ^ dsa_T_acc_2_5815:u32)
dsa_R_SF_1_5817:bool = high:bool(dsa_R_ESI_32_1_5810:u32)
dsa_R_ZF_1_5818:bool = 0:u32 == dsa_R_ESI_32_1_5810:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x2ac3, -1, u32, rw
  @context "R_EDX_32" = 0x2ac3, -1, u32, wr
  @context "R_EFLAGS" = 0x282, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_5819:bool = false
dsa_R_EBP_32_1_5820:u32 = 0xcccccccd:u32
dsa_R_AF_1_5821:bool = false
dsa_R_OF_1_5822:bool = false
dsa_R_SF_1_5823:bool = true
dsa_R_DF_1_5824:bool = false
dsa_R_CF_1_5825:bool = false
dsa_R_EFLAGS_1_5826:u32 = 0x282:u32
dsa_R_PF_1_5827:bool = false
dsa_T_t_1_5828:u64 =
  pad:u64(dsa_R_EAX_32_1_5806:u32) * pad:u64(dsa_R_EBP_32_1_5820:u32)
dsa_R_EAX_32_1_5829:u32 = extract:31:0:[dsa_T_t_1_5828:u64]
dsa_R_EDX_32_1_5830:u32 = extract:63:32:[dsa_T_t_1_5828:u64]
dsa_R_OF_1_5831:bool = extract:63:32:[dsa_T_t_1_5828:u64] <> 0:u32
dsa_R_CF_1_5832:bool = extract:63:32:[dsa_T_t_1_5828:u64] <> 0:u32
dsa_R_SF_1_5833:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_5834:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_5835:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_5836:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x2235, -1, u32, rw
  @context "R_EFLAGS" = 0xa87, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_5837:bool = false
dsa_T_origDEST_1_5838:u32 = dsa_R_EDX_32_1_5830:u32
dsa_T_origCOUNT_1_5839:u32 = 3:u32
dsa_R_EDX_32_1_5840:u32 = dsa_R_EDX_32_1_5830:u32 >> 3:u32
dsa_R_CF_1_5841:bool =
  if dsa_T_origCOUNT_1_5839:u32 == 0:u32 then dsa_R_CF_1_5832:bool else
  high:bool(dsa_T_origDEST_1_5838:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_5839:u32)
dsa_R_OF_1_5842:bool =
  if dsa_T_origCOUNT_1_5839:u32 == 0:u32 then dsa_R_OF_1_5831:bool else
  if dsa_T_origCOUNT_1_5839:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_5838:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_5843:bool =
  if dsa_T_origCOUNT_1_5839:u32 == 0:u32 then dsa_R_SF_1_5833:bool else
  high:bool(dsa_R_EDX_32_1_5840:u32)
dsa_R_ZF_1_5844:bool =
  if dsa_T_origCOUNT_1_5839:u32 == 0:u32 then dsa_R_ZF_1_5834:bool else
  0:u32 == dsa_R_EDX_32_1_5840:u32
dsa_R_PF_3_5847:bool =
  if dsa_T_origCOUNT_1_5839:u32 == 0:u32 then dsa_R_PF_1_5836:bool else
  ~low:bool(let dsa_T_acc_1_5845:u32 :=
                                         dsa_R_EDX_32_1_5840:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_5840:u32 in
            let dsa_T_acc_2_5846:u32 :=
                                         dsa_T_acc_1_5845:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5845:u32 in
            dsa_T_acc_2_5846:u32 >> 1:u32 ^ dsa_T_acc_2_5846:u32)
dsa_R_AF_1_5848:bool =
  if dsa_T_origCOUNT_1_5839:u32 == 0:u32 then dsa_R_AF_1_5835:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x9999a227, -1, u32, wr
  @context "R_EDX_32" = 0x446, -1, u32, rd
  @context "R_EDX_32" = 0x446, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_5849:u32 =
  dsa_R_EDX_32_1_5840:u32 + (dsa_R_EDX_32_1_5840:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x155e, -1, u32, rw
  @context "R_EAX_32" = 0x155e, -1, u32, rd
  @context "R_EFLAGS" = 0x203, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_5850:bool = false
dsa_T_t1_1_5851:u32 = dsa_R_EAX_32_1_5849:u32
dsa_T_t2_1_5852:u32 = dsa_R_EAX_32_1_5849:u32
dsa_R_EAX_32_1_5853:u32 = dsa_R_EAX_32_1_5849:u32 + dsa_T_t2_1_5852:u32
dsa_R_CF_1_5854:bool = dsa_R_EAX_32_1_5853:u32 < dsa_T_t1_1_5851:u32
dsa_R_OF_1_5855:bool =
  high:bool((dsa_T_t1_1_5851:u32 ^ ~dsa_T_t2_1_5852:u32) &
            (dsa_T_t1_1_5851:u32 ^ dsa_R_EAX_32_1_5853:u32))
dsa_R_AF_1_5856:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_5853:u32 ^ dsa_T_t1_1_5851:u32 ^ dsa_T_t2_1_5852:u32))
dsa_R_PF_3_5859:bool =
  ~low:bool(let dsa_T_acc_1_5857:u32 :=
                                         dsa_R_EAX_32_1_5853:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_5853:u32 in
            let dsa_T_acc_2_5858:u32 :=
                                         dsa_T_acc_1_5857:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5857:u32 in
            dsa_T_acc_2_5858:u32 >> 1:u32 ^ dsa_T_acc_2_5858:u32)
dsa_R_SF_1_5860:bool = high:bool(dsa_R_EAX_32_1_5853:u32)
dsa_R_ZF_1_5861:bool = 0:u32 == dsa_R_EAX_32_1_5853:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x2ac3, -1, u32, rw
  @context "R_EAX_32" = 0x2abc, -1, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_5862:bool = false
dsa_T_t_1_5863:u32 = dsa_R_ECX_32_1_5801:u32
dsa_R_ECX_32_1_5864:u32 = dsa_R_ECX_32_1_5801:u32 - dsa_R_EAX_32_1_5853:u32
dsa_R_CF_1_5865:bool = dsa_T_t_1_5863:u32 < dsa_R_EAX_32_1_5853:u32
dsa_R_OF_1_5866:bool =
  high:bool((dsa_T_t_1_5863:u32 ^ dsa_R_EAX_32_1_5853:u32) &
            (dsa_T_t_1_5863:u32 ^ dsa_R_ECX_32_1_5864:u32))
dsa_R_AF_1_5867:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_5864:u32 ^ dsa_T_t_1_5863:u32 ^ dsa_R_EAX_32_1_5853:u32))
dsa_R_PF_3_5870:bool =
  ~low:bool(let dsa_T_acc_1_5868:u32 :=
                                         dsa_R_ECX_32_1_5864:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_5864:u32 in
            let dsa_T_acc_2_5869:u32 :=
                                         dsa_T_acc_1_5868:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5868:u32 in
            dsa_T_acc_2_5869:u32 >> 1:u32 ^ dsa_T_acc_2_5869:u32)
dsa_R_SF_1_5871:bool = high:bool(dsa_R_ECX_32_1_5864:u32)
dsa_R_ZF_1_5872:bool = 0:u32 == dsa_R_ECX_32_1_5864:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x446, -1, u32, rd
  @context "R_EDX_32" = 0x446, -1, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_5873:bool = false
dsa_T_t_1_5874:u32 = dsa_R_EDX_32_1_5840:u32 & dsa_R_EDX_32_1_5840:u32
dsa_R_OF_1_5875:bool = false
dsa_R_CF_1_5876:bool = false
dsa_R_AF_1_5877:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_5880:bool =
  ~low:bool(let dsa_T_acc_1_5878:u32 :=
                                         dsa_T_t_1_5874:u32 >> 4:u32 ^
                                         dsa_T_t_1_5874:u32 in
            let dsa_T_acc_2_5879:u32 :=
                                         dsa_T_acc_1_5878:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5878:u32 in
            dsa_T_acc_2_5879:u32 >> 1:u32 ^ dsa_T_acc_2_5879:u32)
dsa_R_SF_1_5881:bool = high:bool(dsa_T_t_1_5874:u32)
dsa_R_ZF_1_5882:bool = 0:u32 == dsa_T_t_1_5874:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x2abc, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x7, -1, u32, rd
  @context "mem32[0xdd01cc67]" = 0x37, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc67_1_5883:u8 = low:u8(0x37:u8)
dsa_R_EDI_32_1_5884:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_5885:u32 = pad:u32(pad:u8(dsa_mem_dd01cc67_1_5883:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x7, -1, u32, wr
  @context "R_EDX_32" = 0x446, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_5886:u32 = dsa_R_EDX_32_1_5840:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf067a, 0, u32, rd
  @context "R_EAX_32" = 0x37, -1, u32, rd
  @context "mem32[0xffaf067a]" = 0x37, -1, u8, wr
label pc_0xdcf03221
dsa_R_ESI_32_1_5887:u32 = 0xffaf067a:u32
dsa_mem_ffaf067a_1_5888:u8 = low:u8(low:u8(dsa_R_EAX_32_1_5885:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_5889:bool = false
dsa_R_EIP_1_5890:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_5882:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp144"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x37, -1, u32, wr
  @context "R_ECX_32" = 0x446, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_5891:u32 = dsa_R_ECX_32_1_5886:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf067a, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_5892:u32 = 0xffaf067a:u32
dsa_R_DF_1_5893:bool = false
dsa_T_t_1_5894:u32 = dsa_R_ESI_32_1_5892:u32
dsa_R_ESI_32_1_5895:u32 = dsa_R_ESI_32_1_5892:u32 - 1:u32
dsa_R_CF_1_5896:bool = dsa_T_t_1_5894:u32 < 1:u32
dsa_R_OF_1_5897:bool =
  high:bool((dsa_T_t_1_5894:u32 ^ 1:u32) &
            (dsa_T_t_1_5894:u32 ^ dsa_R_ESI_32_1_5895:u32))
dsa_R_AF_1_5898:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_5895:u32 ^ dsa_T_t_1_5894:u32 ^ 1:u32))
dsa_R_PF_3_5901:bool =
  ~low:bool(let dsa_T_acc_1_5899:u32 :=
                                         dsa_R_ESI_32_1_5895:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_5895:u32 in
            let dsa_T_acc_2_5900:u32 :=
                                         dsa_T_acc_1_5899:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5899:u32 in
            dsa_T_acc_2_5900:u32 >> 1:u32 ^ dsa_T_acc_2_5900:u32)
dsa_R_SF_1_5902:bool = high:bool(dsa_R_ESI_32_1_5895:u32)
dsa_R_ZF_1_5903:bool = 0:u32 == dsa_R_ESI_32_1_5895:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x446, -1, u32, rw
  @context "R_EDX_32" = 0x446, -1, u32, wr
  @context "R_EFLAGS" = 0x282, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_5904:bool = false
dsa_R_EBP_32_1_5905:u32 = 0xcccccccd:u32
dsa_R_AF_1_5906:bool = false
dsa_R_OF_1_5907:bool = false
dsa_R_SF_1_5908:bool = true
dsa_R_DF_1_5909:bool = false
dsa_R_CF_1_5910:bool = false
dsa_R_EFLAGS_1_5911:u32 = 0x282:u32
dsa_R_PF_1_5912:bool = false
dsa_T_t_1_5913:u64 =
  pad:u64(dsa_R_EAX_32_1_5891:u32) * pad:u64(dsa_R_EBP_32_1_5905:u32)
dsa_R_EAX_32_1_5914:u32 = extract:31:0:[dsa_T_t_1_5913:u64]
dsa_R_EDX_32_1_5915:u32 = extract:63:32:[dsa_T_t_1_5913:u64]
dsa_R_OF_1_5916:bool = extract:63:32:[dsa_T_t_1_5913:u64] <> 0:u32
dsa_R_CF_1_5917:bool = extract:63:32:[dsa_T_t_1_5913:u64] <> 0:u32
dsa_R_SF_1_5918:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_5919:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_5920:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_5921:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x36b, -1, u32, rw
  @context "R_EFLAGS" = 0xa03, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_5922:bool = false
dsa_T_origDEST_1_5923:u32 = dsa_R_EDX_32_1_5915:u32
dsa_T_origCOUNT_1_5924:u32 = 3:u32
dsa_R_EDX_32_1_5925:u32 = dsa_R_EDX_32_1_5915:u32 >> 3:u32
dsa_R_CF_1_5926:bool =
  if dsa_T_origCOUNT_1_5924:u32 == 0:u32 then dsa_R_CF_1_5917:bool else
  high:bool(dsa_T_origDEST_1_5923:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_5924:u32)
dsa_R_OF_1_5927:bool =
  if dsa_T_origCOUNT_1_5924:u32 == 0:u32 then dsa_R_OF_1_5916:bool else
  if dsa_T_origCOUNT_1_5924:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_5923:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_5928:bool =
  if dsa_T_origCOUNT_1_5924:u32 == 0:u32 then dsa_R_SF_1_5918:bool else
  high:bool(dsa_R_EDX_32_1_5925:u32)
dsa_R_ZF_1_5929:bool =
  if dsa_T_origCOUNT_1_5924:u32 == 0:u32 then dsa_R_ZF_1_5919:bool else
  0:u32 == dsa_R_EDX_32_1_5925:u32
dsa_R_PF_3_5932:bool =
  if dsa_T_origCOUNT_1_5924:u32 == 0:u32 then dsa_R_PF_1_5921:bool else
  ~low:bool(let dsa_T_acc_1_5930:u32 :=
                                         dsa_R_EDX_32_1_5925:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_5925:u32 in
            let dsa_T_acc_2_5931:u32 :=
                                         dsa_T_acc_1_5930:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5930:u32 in
            dsa_T_acc_2_5931:u32 >> 1:u32 ^ dsa_T_acc_2_5931:u32)
dsa_R_AF_1_5933:bool =
  if dsa_T_origCOUNT_1_5924:u32 == 0:u32 then dsa_R_AF_1_5920:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x3333340e, -1, u32, wr
  @context "R_EDX_32" = 0x6d, -1, u32, rd
  @context "R_EDX_32" = 0x6d, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_5934:u32 =
  dsa_R_EDX_32_1_5925:u32 + (dsa_R_EDX_32_1_5925:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x221, -1, u32, rw
  @context "R_EAX_32" = 0x221, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_5935:bool = false
dsa_T_t1_1_5936:u32 = dsa_R_EAX_32_1_5934:u32
dsa_T_t2_1_5937:u32 = dsa_R_EAX_32_1_5934:u32
dsa_R_EAX_32_1_5938:u32 = dsa_R_EAX_32_1_5934:u32 + dsa_T_t2_1_5937:u32
dsa_R_CF_1_5939:bool = dsa_R_EAX_32_1_5938:u32 < dsa_T_t1_1_5936:u32
dsa_R_OF_1_5940:bool =
  high:bool((dsa_T_t1_1_5936:u32 ^ ~dsa_T_t2_1_5937:u32) &
            (dsa_T_t1_1_5936:u32 ^ dsa_R_EAX_32_1_5938:u32))
dsa_R_AF_1_5941:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_5938:u32 ^ dsa_T_t1_1_5936:u32 ^ dsa_T_t2_1_5937:u32))
dsa_R_PF_3_5944:bool =
  ~low:bool(let dsa_T_acc_1_5942:u32 :=
                                         dsa_R_EAX_32_1_5938:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_5938:u32 in
            let dsa_T_acc_2_5943:u32 :=
                                         dsa_T_acc_1_5942:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5942:u32 in
            dsa_T_acc_2_5943:u32 >> 1:u32 ^ dsa_T_acc_2_5943:u32)
dsa_R_SF_1_5945:bool = high:bool(dsa_R_EAX_32_1_5938:u32)
dsa_R_ZF_1_5946:bool = 0:u32 == dsa_R_EAX_32_1_5938:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x446, -1, u32, rw
  @context "R_EAX_32" = 0x442, -1, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_5947:bool = false
dsa_T_t_1_5948:u32 = dsa_R_ECX_32_1_5886:u32
dsa_R_ECX_32_1_5949:u32 = dsa_R_ECX_32_1_5886:u32 - dsa_R_EAX_32_1_5938:u32
dsa_R_CF_1_5950:bool = dsa_T_t_1_5948:u32 < dsa_R_EAX_32_1_5938:u32
dsa_R_OF_1_5951:bool =
  high:bool((dsa_T_t_1_5948:u32 ^ dsa_R_EAX_32_1_5938:u32) &
            (dsa_T_t_1_5948:u32 ^ dsa_R_ECX_32_1_5949:u32))
dsa_R_AF_1_5952:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_5949:u32 ^ dsa_T_t_1_5948:u32 ^ dsa_R_EAX_32_1_5938:u32))
dsa_R_PF_3_5955:bool =
  ~low:bool(let dsa_T_acc_1_5953:u32 :=
                                         dsa_R_ECX_32_1_5949:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_5949:u32 in
            let dsa_T_acc_2_5954:u32 :=
                                         dsa_T_acc_1_5953:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5953:u32 in
            dsa_T_acc_2_5954:u32 >> 1:u32 ^ dsa_T_acc_2_5954:u32)
dsa_R_SF_1_5956:bool = high:bool(dsa_R_ECX_32_1_5949:u32)
dsa_R_ZF_1_5957:bool = 0:u32 == dsa_R_ECX_32_1_5949:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x6d, -1, u32, rd
  @context "R_EDX_32" = 0x6d, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_5958:bool = false
dsa_T_t_1_5959:u32 = dsa_R_EDX_32_1_5925:u32 & dsa_R_EDX_32_1_5925:u32
dsa_R_OF_1_5960:bool = false
dsa_R_CF_1_5961:bool = false
dsa_R_AF_1_5962:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_5965:bool =
  ~low:bool(let dsa_T_acc_1_5963:u32 :=
                                         dsa_T_t_1_5959:u32 >> 4:u32 ^
                                         dsa_T_t_1_5959:u32 in
            let dsa_T_acc_2_5964:u32 :=
                                         dsa_T_acc_1_5963:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5963:u32 in
            dsa_T_acc_2_5964:u32 >> 1:u32 ^ dsa_T_acc_2_5964:u32)
dsa_R_SF_1_5966:bool = high:bool(dsa_T_t_1_5959:u32)
dsa_R_ZF_1_5967:bool = 0:u32 == dsa_T_t_1_5959:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x442, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x4, -1, u32, rd
  @context "mem32[0xdd01cc64]" = 0x34, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc64_1_5968:u8 = low:u8(0x34:u8)
dsa_R_EDI_32_1_5969:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_5970:u32 = pad:u32(pad:u8(dsa_mem_dd01cc64_1_5968:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x4, -1, u32, wr
  @context "R_EDX_32" = 0x6d, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_5971:u32 = dsa_R_EDX_32_1_5925:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf0679, 0, u32, rd
  @context "R_EAX_32" = 0x34, -1, u32, rd
  @context "mem32[0xffaf0679]" = 0x34, -1, u8, wr
label pc_0xdcf03221
dsa_R_ESI_32_1_5972:u32 = 0xffaf0679:u32
dsa_mem_ffaf0679_1_5973:u8 = low:u8(low:u8(dsa_R_EAX_32_1_5970:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_5974:bool = false
dsa_R_EIP_1_5975:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_5967:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp145"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x34, -1, u32, wr
  @context "R_ECX_32" = 0x6d, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_5976:u32 = dsa_R_ECX_32_1_5971:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf0679, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_5977:u32 = 0xffaf0679:u32
dsa_R_DF_1_5978:bool = false
dsa_T_t_1_5979:u32 = dsa_R_ESI_32_1_5977:u32
dsa_R_ESI_32_1_5980:u32 = dsa_R_ESI_32_1_5977:u32 - 1:u32
dsa_R_CF_1_5981:bool = dsa_T_t_1_5979:u32 < 1:u32
dsa_R_OF_1_5982:bool =
  high:bool((dsa_T_t_1_5979:u32 ^ 1:u32) &
            (dsa_T_t_1_5979:u32 ^ dsa_R_ESI_32_1_5980:u32))
dsa_R_AF_1_5983:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_5980:u32 ^ dsa_T_t_1_5979:u32 ^ 1:u32))
dsa_R_PF_3_5986:bool =
  ~low:bool(let dsa_T_acc_1_5984:u32 :=
                                         dsa_R_ESI_32_1_5980:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_5980:u32 in
            let dsa_T_acc_2_5985:u32 :=
                                         dsa_T_acc_1_5984:u32 >> 2:u32 ^
                                         dsa_T_acc_1_5984:u32 in
            dsa_T_acc_2_5985:u32 >> 1:u32 ^ dsa_T_acc_2_5985:u32)
dsa_R_SF_1_5987:bool = high:bool(dsa_R_ESI_32_1_5980:u32)
dsa_R_ZF_1_5988:bool = 0:u32 == dsa_R_ESI_32_1_5980:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x6d, -1, u32, rw
  @context "R_EDX_32" = 0x6d, -1, u32, wr
  @context "R_EFLAGS" = 0x286, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_5989:bool = false
dsa_R_EBP_32_1_5990:u32 = 0xcccccccd:u32
dsa_R_AF_1_5991:bool = false
dsa_R_OF_1_5992:bool = false
dsa_R_SF_1_5993:bool = true
dsa_R_DF_1_5994:bool = false
dsa_R_CF_1_5995:bool = false
dsa_R_EFLAGS_1_5996:u32 = 0x286:u32
dsa_R_PF_1_5997:bool = true
dsa_T_t_1_5998:u64 =
  pad:u64(dsa_R_EAX_32_1_5976:u32) * pad:u64(dsa_R_EBP_32_1_5990:u32)
dsa_R_EAX_32_1_5999:u32 = extract:31:0:[dsa_T_t_1_5998:u64]
dsa_R_EDX_32_1_6000:u32 = extract:63:32:[dsa_T_t_1_5998:u64]
dsa_R_OF_1_6001:bool = extract:63:32:[dsa_T_t_1_5998:u64] <> 0:u32
dsa_R_CF_1_6002:bool = extract:63:32:[dsa_T_t_1_5998:u64] <> 0:u32
dsa_R_SF_1_6003:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_6004:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_6005:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_6006:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x57, -1, u32, rw
  @context "R_EFLAGS" = 0xa03, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_6007:bool = false
dsa_T_origDEST_1_6008:u32 = dsa_R_EDX_32_1_6000:u32
dsa_T_origCOUNT_1_6009:u32 = 3:u32
dsa_R_EDX_32_1_6010:u32 = dsa_R_EDX_32_1_6000:u32 >> 3:u32
dsa_R_CF_1_6011:bool =
  if dsa_T_origCOUNT_1_6009:u32 == 0:u32 then dsa_R_CF_1_6002:bool else
  high:bool(dsa_T_origDEST_1_6008:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_6009:u32)
dsa_R_OF_1_6012:bool =
  if dsa_T_origCOUNT_1_6009:u32 == 0:u32 then dsa_R_OF_1_6001:bool else
  if dsa_T_origCOUNT_1_6009:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_6008:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_6013:bool =
  if dsa_T_origCOUNT_1_6009:u32 == 0:u32 then dsa_R_SF_1_6003:bool else
  high:bool(dsa_R_EDX_32_1_6010:u32)
dsa_R_ZF_1_6014:bool =
  if dsa_T_origCOUNT_1_6009:u32 == 0:u32 then dsa_R_ZF_1_6004:bool else
  0:u32 == dsa_R_EDX_32_1_6010:u32
dsa_R_PF_3_6017:bool =
  if dsa_T_origCOUNT_1_6009:u32 == 0:u32 then dsa_R_PF_1_6006:bool else
  ~low:bool(let dsa_T_acc_1_6015:u32 :=
                                         dsa_R_EDX_32_1_6010:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_6010:u32 in
            let dsa_T_acc_2_6016:u32 :=
                                         dsa_T_acc_1_6015:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6015:u32 in
            dsa_T_acc_2_6016:u32 >> 1:u32 ^ dsa_T_acc_2_6016:u32)
dsa_R_AF_1_6018:bool =
  if dsa_T_origCOUNT_1_6009:u32 == 0:u32 then dsa_R_AF_1_6005:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x33333349, -1, u32, wr
  @context "R_EDX_32" = 0xa, -1, u32, rd
  @context "R_EDX_32" = 0xa, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_6019:u32 =
  dsa_R_EDX_32_1_6010:u32 + (dsa_R_EDX_32_1_6010:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x32, -1, u32, rw
  @context "R_EAX_32" = 0x32, -1, u32, rd
  @context "R_EFLAGS" = 0x207, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_6020:bool = false
dsa_T_t1_1_6021:u32 = dsa_R_EAX_32_1_6019:u32
dsa_T_t2_1_6022:u32 = dsa_R_EAX_32_1_6019:u32
dsa_R_EAX_32_1_6023:u32 = dsa_R_EAX_32_1_6019:u32 + dsa_T_t2_1_6022:u32
dsa_R_CF_1_6024:bool = dsa_R_EAX_32_1_6023:u32 < dsa_T_t1_1_6021:u32
dsa_R_OF_1_6025:bool =
  high:bool((dsa_T_t1_1_6021:u32 ^ ~dsa_T_t2_1_6022:u32) &
            (dsa_T_t1_1_6021:u32 ^ dsa_R_EAX_32_1_6023:u32))
dsa_R_AF_1_6026:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_6023:u32 ^ dsa_T_t1_1_6021:u32 ^ dsa_T_t2_1_6022:u32))
dsa_R_PF_3_6029:bool =
  ~low:bool(let dsa_T_acc_1_6027:u32 :=
                                         dsa_R_EAX_32_1_6023:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_6023:u32 in
            let dsa_T_acc_2_6028:u32 :=
                                         dsa_T_acc_1_6027:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6027:u32 in
            dsa_T_acc_2_6028:u32 >> 1:u32 ^ dsa_T_acc_2_6028:u32)
dsa_R_SF_1_6030:bool = high:bool(dsa_R_EAX_32_1_6023:u32)
dsa_R_ZF_1_6031:bool = 0:u32 == dsa_R_EAX_32_1_6023:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x6d, -1, u32, rw
  @context "R_EAX_32" = 0x64, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_6032:bool = false
dsa_T_t_1_6033:u32 = dsa_R_ECX_32_1_5971:u32
dsa_R_ECX_32_1_6034:u32 = dsa_R_ECX_32_1_5971:u32 - dsa_R_EAX_32_1_6023:u32
dsa_R_CF_1_6035:bool = dsa_T_t_1_6033:u32 < dsa_R_EAX_32_1_6023:u32
dsa_R_OF_1_6036:bool =
  high:bool((dsa_T_t_1_6033:u32 ^ dsa_R_EAX_32_1_6023:u32) &
            (dsa_T_t_1_6033:u32 ^ dsa_R_ECX_32_1_6034:u32))
dsa_R_AF_1_6037:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_6034:u32 ^ dsa_T_t_1_6033:u32 ^ dsa_R_EAX_32_1_6023:u32))
dsa_R_PF_3_6040:bool =
  ~low:bool(let dsa_T_acc_1_6038:u32 :=
                                         dsa_R_ECX_32_1_6034:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_6034:u32 in
            let dsa_T_acc_2_6039:u32 :=
                                         dsa_T_acc_1_6038:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6038:u32 in
            dsa_T_acc_2_6039:u32 >> 1:u32 ^ dsa_T_acc_2_6039:u32)
dsa_R_SF_1_6041:bool = high:bool(dsa_R_ECX_32_1_6034:u32)
dsa_R_ZF_1_6042:bool = 0:u32 == dsa_R_ECX_32_1_6034:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0xa, -1, u32, rd
  @context "R_EDX_32" = 0xa, -1, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_6043:bool = false
dsa_T_t_1_6044:u32 = dsa_R_EDX_32_1_6010:u32 & dsa_R_EDX_32_1_6010:u32
dsa_R_OF_1_6045:bool = false
dsa_R_CF_1_6046:bool = false
dsa_R_AF_1_6047:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_6050:bool =
  ~low:bool(let dsa_T_acc_1_6048:u32 :=
                                         dsa_T_t_1_6044:u32 >> 4:u32 ^
                                         dsa_T_t_1_6044:u32 in
            let dsa_T_acc_2_6049:u32 :=
                                         dsa_T_acc_1_6048:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6048:u32 in
            dsa_T_acc_2_6049:u32 >> 1:u32 ^ dsa_T_acc_2_6049:u32)
dsa_R_SF_1_6051:bool = high:bool(dsa_T_t_1_6044:u32)
dsa_R_ZF_1_6052:bool = 0:u32 == dsa_T_t_1_6044:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x64, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x9, -1, u32, rd
  @context "mem32[0xdd01cc69]" = 0x39, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc69_1_6053:u8 = low:u8(0x39:u8)
dsa_R_EDI_32_1_6054:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_6055:u32 = pad:u32(pad:u8(dsa_mem_dd01cc69_1_6053:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x9, -1, u32, wr
  @context "R_EDX_32" = 0xa, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_6056:u32 = dsa_R_EDX_32_1_6010:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf0678, 0, u32, rd
  @context "R_EAX_32" = 0x39, -1, u32, rd
  @context "mem32[0xffaf0678]" = 0x39, -1, u8, wr
label pc_0xdcf03221
dsa_R_ESI_32_1_6057:u32 = 0xffaf0678:u32
dsa_mem_ffaf0678_1_6058:u8 = low:u8(low:u8(dsa_R_EAX_32_1_6055:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_6059:bool = false
dsa_R_EIP_1_6060:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_6052:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp146"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x39, -1, u32, wr
  @context "R_ECX_32" = 0xa, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_6061:u32 = dsa_R_ECX_32_1_6056:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf0678, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_6062:u32 = 0xffaf0678:u32
dsa_R_DF_1_6063:bool = false
dsa_T_t_1_6064:u32 = dsa_R_ESI_32_1_6062:u32
dsa_R_ESI_32_1_6065:u32 = dsa_R_ESI_32_1_6062:u32 - 1:u32
dsa_R_CF_1_6066:bool = dsa_T_t_1_6064:u32 < 1:u32
dsa_R_OF_1_6067:bool =
  high:bool((dsa_T_t_1_6064:u32 ^ 1:u32) &
            (dsa_T_t_1_6064:u32 ^ dsa_R_ESI_32_1_6065:u32))
dsa_R_AF_1_6068:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_6065:u32 ^ dsa_T_t_1_6064:u32 ^ 1:u32))
dsa_R_PF_3_6071:bool =
  ~low:bool(let dsa_T_acc_1_6069:u32 :=
                                         dsa_R_ESI_32_1_6065:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_6065:u32 in
            let dsa_T_acc_2_6070:u32 :=
                                         dsa_T_acc_1_6069:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6069:u32 in
            dsa_T_acc_2_6070:u32 >> 1:u32 ^ dsa_T_acc_2_6070:u32)
dsa_R_SF_1_6072:bool = high:bool(dsa_R_ESI_32_1_6065:u32)
dsa_R_ZF_1_6073:bool = 0:u32 == dsa_R_ESI_32_1_6065:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0xa, -1, u32, rw
  @context "R_EDX_32" = 0xa, -1, u32, wr
  @context "R_EFLAGS" = 0x286, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_6074:bool = false
dsa_R_EBP_32_1_6075:u32 = 0xcccccccd:u32
dsa_R_AF_1_6076:bool = false
dsa_R_OF_1_6077:bool = false
dsa_R_SF_1_6078:bool = true
dsa_R_DF_1_6079:bool = false
dsa_R_CF_1_6080:bool = false
dsa_R_EFLAGS_1_6081:u32 = 0x286:u32
dsa_R_PF_1_6082:bool = true
dsa_T_t_1_6083:u64 =
  pad:u64(dsa_R_EAX_32_1_6061:u32) * pad:u64(dsa_R_EBP_32_1_6075:u32)
dsa_R_EAX_32_1_6084:u32 = extract:31:0:[dsa_T_t_1_6083:u64]
dsa_R_EDX_32_1_6085:u32 = extract:63:32:[dsa_T_t_1_6083:u64]
dsa_R_OF_1_6086:bool = extract:63:32:[dsa_T_t_1_6083:u64] <> 0:u32
dsa_R_CF_1_6087:bool = extract:63:32:[dsa_T_t_1_6083:u64] <> 0:u32
dsa_R_SF_1_6088:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_6089:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_6090:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_6091:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x8, -1, u32, rw
  @context "R_EFLAGS" = 0xa03, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_6092:bool = false
dsa_T_origDEST_1_6093:u32 = dsa_R_EDX_32_1_6085:u32
dsa_T_origCOUNT_1_6094:u32 = 3:u32
dsa_R_EDX_32_1_6095:u32 = dsa_R_EDX_32_1_6085:u32 >> 3:u32
dsa_R_CF_1_6096:bool =
  if dsa_T_origCOUNT_1_6094:u32 == 0:u32 then dsa_R_CF_1_6087:bool else
  high:bool(dsa_T_origDEST_1_6093:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_6094:u32)
dsa_R_OF_1_6097:bool =
  if dsa_T_origCOUNT_1_6094:u32 == 0:u32 then dsa_R_OF_1_6086:bool else
  if dsa_T_origCOUNT_1_6094:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_6093:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_6098:bool =
  if dsa_T_origCOUNT_1_6094:u32 == 0:u32 then dsa_R_SF_1_6088:bool else
  high:bool(dsa_R_EDX_32_1_6095:u32)
dsa_R_ZF_1_6099:bool =
  if dsa_T_origCOUNT_1_6094:u32 == 0:u32 then dsa_R_ZF_1_6089:bool else
  0:u32 == dsa_R_EDX_32_1_6095:u32
dsa_R_PF_3_6102:bool =
  if dsa_T_origCOUNT_1_6094:u32 == 0:u32 then dsa_R_PF_1_6091:bool else
  ~low:bool(let dsa_T_acc_1_6100:u32 :=
                                         dsa_R_EDX_32_1_6095:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_6095:u32 in
            let dsa_T_acc_2_6101:u32 :=
                                         dsa_T_acc_1_6100:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6100:u32 in
            dsa_T_acc_2_6101:u32 >> 1:u32 ^ dsa_T_acc_2_6101:u32)
dsa_R_AF_1_6103:bool =
  if dsa_T_origCOUNT_1_6094:u32 == 0:u32 then dsa_R_AF_1_6090:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0x2, -1, u32, wr
  @context "R_EDX_32" = 0x1, -1, u32, rd
  @context "R_EDX_32" = 0x1, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_6104:u32 =
  dsa_R_EDX_32_1_6095:u32 + (dsa_R_EDX_32_1_6095:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x5, -1, u32, rw
  @context "R_EAX_32" = 0x5, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_6105:bool = false
dsa_T_t1_1_6106:u32 = dsa_R_EAX_32_1_6104:u32
dsa_T_t2_1_6107:u32 = dsa_R_EAX_32_1_6104:u32
dsa_R_EAX_32_1_6108:u32 = dsa_R_EAX_32_1_6104:u32 + dsa_T_t2_1_6107:u32
dsa_R_CF_1_6109:bool = dsa_R_EAX_32_1_6108:u32 < dsa_T_t1_1_6106:u32
dsa_R_OF_1_6110:bool =
  high:bool((dsa_T_t1_1_6106:u32 ^ ~dsa_T_t2_1_6107:u32) &
            (dsa_T_t1_1_6106:u32 ^ dsa_R_EAX_32_1_6108:u32))
dsa_R_AF_1_6111:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_6108:u32 ^ dsa_T_t1_1_6106:u32 ^ dsa_T_t2_1_6107:u32))
dsa_R_PF_3_6114:bool =
  ~low:bool(let dsa_T_acc_1_6112:u32 :=
                                         dsa_R_EAX_32_1_6108:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_6108:u32 in
            let dsa_T_acc_2_6113:u32 :=
                                         dsa_T_acc_1_6112:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6112:u32 in
            dsa_T_acc_2_6113:u32 >> 1:u32 ^ dsa_T_acc_2_6113:u32)
dsa_R_SF_1_6115:bool = high:bool(dsa_R_EAX_32_1_6108:u32)
dsa_R_ZF_1_6116:bool = 0:u32 == dsa_R_EAX_32_1_6108:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0xa, -1, u32, rw
  @context "R_EAX_32" = 0xa, -1, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_6117:bool = false
dsa_T_t_1_6118:u32 = dsa_R_ECX_32_1_6056:u32
dsa_R_ECX_32_1_6119:u32 = dsa_R_ECX_32_1_6056:u32 - dsa_R_EAX_32_1_6108:u32
dsa_R_CF_1_6120:bool = dsa_T_t_1_6118:u32 < dsa_R_EAX_32_1_6108:u32
dsa_R_OF_1_6121:bool =
  high:bool((dsa_T_t_1_6118:u32 ^ dsa_R_EAX_32_1_6108:u32) &
            (dsa_T_t_1_6118:u32 ^ dsa_R_ECX_32_1_6119:u32))
dsa_R_AF_1_6122:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_6119:u32 ^ dsa_T_t_1_6118:u32 ^ dsa_R_EAX_32_1_6108:u32))
dsa_R_PF_3_6125:bool =
  ~low:bool(let dsa_T_acc_1_6123:u32 :=
                                         dsa_R_ECX_32_1_6119:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_6119:u32 in
            let dsa_T_acc_2_6124:u32 :=
                                         dsa_T_acc_1_6123:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6123:u32 in
            dsa_T_acc_2_6124:u32 >> 1:u32 ^ dsa_T_acc_2_6124:u32)
dsa_R_SF_1_6126:bool = high:bool(dsa_R_ECX_32_1_6119:u32)
dsa_R_ZF_1_6127:bool = 0:u32 == dsa_R_ECX_32_1_6119:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x1, -1, u32, rd
  @context "R_EDX_32" = 0x1, -1, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_6128:bool = false
dsa_T_t_1_6129:u32 = dsa_R_EDX_32_1_6095:u32 & dsa_R_EDX_32_1_6095:u32
dsa_R_OF_1_6130:bool = false
dsa_R_CF_1_6131:bool = false
dsa_R_AF_1_6132:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_6135:bool =
  ~low:bool(let dsa_T_acc_1_6133:u32 :=
                                         dsa_T_t_1_6129:u32 >> 4:u32 ^
                                         dsa_T_t_1_6129:u32 in
            let dsa_T_acc_2_6134:u32 :=
                                         dsa_T_acc_1_6133:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6133:u32 in
            dsa_T_acc_2_6134:u32 >> 1:u32 ^ dsa_T_acc_2_6134:u32)
dsa_R_SF_1_6136:bool = high:bool(dsa_T_t_1_6129:u32)
dsa_R_ZF_1_6137:bool = 0:u32 == dsa_T_t_1_6129:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0xa, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x0, -1, u32, rd
  @context "mem32[0xdd01cc60]" = 0x30, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc60_1_6138:u8 = low:u8(0x30:u8)
dsa_R_EDI_32_1_6139:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_6140:u32 = pad:u32(pad:u8(dsa_mem_dd01cc60_1_6138:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x0, -1, u32, wr
  @context "R_EDX_32" = 0x1, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_6141:u32 = dsa_R_EDX_32_1_6095:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf0677, 0, u32, rd
  @context "R_EAX_32" = 0x30, -1, u32, rd
  @context "mem32[0xffaf0677]" = 0x30, -1, u8, wr
label pc_0xdcf03221
dsa_R_ESI_32_1_6142:u32 = 0xffaf0677:u32
dsa_mem_ffaf0677_1_6143:u8 = low:u8(low:u8(dsa_R_EAX_32_1_6140:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_6144:bool = false
dsa_R_EIP_1_6145:u32 = 0xdcf03223:u32
assert ~dsa_R_ZF_1_6137:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp147"*/
addr 0xdcf03208 @asm "mov    eax,ecx" @tid "0"
  @context "R_EAX_32" = 0x30, -1, u32, wr
  @context "R_ECX_32" = 0x1, -1, u32, rd
label pc_0xdcf03208
dsa_R_EAX_32_1_6146:u32 = dsa_R_ECX_32_1_6141:u32
addr 0xdcf0320a @asm "sub    esi,0x1" @tid "0"
  @context "R_ESI_32" = 0xffaf0677, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf0320a
dsa_R_ESI_32_1_6147:u32 = 0xffaf0677:u32
dsa_R_DF_1_6148:bool = false
dsa_T_t_1_6149:u32 = dsa_R_ESI_32_1_6147:u32
dsa_R_ESI_32_1_6150:u32 = dsa_R_ESI_32_1_6147:u32 - 1:u32
dsa_R_CF_1_6151:bool = dsa_T_t_1_6149:u32 < 1:u32
dsa_R_OF_1_6152:bool =
  high:bool((dsa_T_t_1_6149:u32 ^ 1:u32) &
            (dsa_T_t_1_6149:u32 ^ dsa_R_ESI_32_1_6150:u32))
dsa_R_AF_1_6153:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ESI_32_1_6150:u32 ^ dsa_T_t_1_6149:u32 ^ 1:u32))
dsa_R_PF_3_6156:bool =
  ~low:bool(let dsa_T_acc_1_6154:u32 :=
                                         dsa_R_ESI_32_1_6150:u32 >> 4:u32 ^
                                         dsa_R_ESI_32_1_6150:u32 in
            let dsa_T_acc_2_6155:u32 :=
                                         dsa_T_acc_1_6154:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6154:u32 in
            dsa_T_acc_2_6155:u32 >> 1:u32 ^ dsa_T_acc_2_6155:u32)
dsa_R_SF_1_6157:bool = high:bool(dsa_R_ESI_32_1_6150:u32)
dsa_R_ZF_1_6158:bool = 0:u32 == dsa_R_ESI_32_1_6150:u32
addr 0xdcf0320d @asm "mul    ebp" @tid "0"
  @context "R_EBP_32" = 0xcccccccd, 0, u32, rd
  @context "R_EAX_32" = 0x1, -1, u32, rw
  @context "R_EDX_32" = 0x1, -1, u32, wr
  @context "R_EFLAGS" = 0x282, 0, u32, wr
label pc_0xdcf0320d
dsa_R_ZF_1_6159:bool = false
dsa_R_EBP_32_1_6160:u32 = 0xcccccccd:u32
dsa_R_AF_1_6161:bool = false
dsa_R_OF_1_6162:bool = false
dsa_R_SF_1_6163:bool = true
dsa_R_DF_1_6164:bool = false
dsa_R_CF_1_6165:bool = false
dsa_R_EFLAGS_1_6166:u32 = 0x282:u32
dsa_R_PF_1_6167:bool = false
dsa_T_t_1_6168:u64 =
  pad:u64(dsa_R_EAX_32_1_6146:u32) * pad:u64(dsa_R_EBP_32_1_6160:u32)
dsa_R_EAX_32_1_6169:u32 = extract:31:0:[dsa_T_t_1_6168:u64]
dsa_R_EDX_32_1_6170:u32 = extract:63:32:[dsa_T_t_1_6168:u64]
dsa_R_OF_1_6171:bool = extract:63:32:[dsa_T_t_1_6168:u64] <> 0:u32
dsa_R_CF_1_6172:bool = extract:63:32:[dsa_T_t_1_6168:u64] <> 0:u32
dsa_R_SF_1_6173:bool = unknown "SF is undefined after Mul":bool
dsa_R_ZF_1_6174:bool = unknown "ZF is undefined after Mul":bool
dsa_R_AF_1_6175:bool = unknown "AF is undefined after Mul":bool
dsa_R_PF_1_6176:bool = unknown "PF is undefined after Mul":bool
addr 0xdcf0320f @asm "shr    edx,0x3" @tid "0"
  @context "R_EDX_32" = 0x0, -1, u32, rw
  @context "R_EFLAGS" = 0x282, -1, u32, wr
label pc_0xdcf0320f
dsa_R_DF_1_6177:bool = false
dsa_T_origDEST_1_6178:u32 = dsa_R_EDX_32_1_6170:u32
dsa_T_origCOUNT_1_6179:u32 = 3:u32
dsa_R_EDX_32_1_6180:u32 = dsa_R_EDX_32_1_6170:u32 >> 3:u32
dsa_R_CF_1_6181:bool =
  if dsa_T_origCOUNT_1_6179:u32 == 0:u32 then dsa_R_CF_1_6172:bool else
  high:bool(dsa_T_origDEST_1_6178:u32 <<
            0x20:u32 - dsa_T_origCOUNT_1_6179:u32)
dsa_R_OF_1_6182:bool =
  if dsa_T_origCOUNT_1_6179:u32 == 0:u32 then dsa_R_OF_1_6171:bool else
  if dsa_T_origCOUNT_1_6179:u32 == 1:u32 then
  high:bool(dsa_T_origDEST_1_6178:u32) else
  unknown "OF undefined after shift":bool
dsa_R_SF_1_6183:bool =
  if dsa_T_origCOUNT_1_6179:u32 == 0:u32 then dsa_R_SF_1_6173:bool else
  high:bool(dsa_R_EDX_32_1_6180:u32)
dsa_R_ZF_1_6184:bool =
  if dsa_T_origCOUNT_1_6179:u32 == 0:u32 then dsa_R_ZF_1_6174:bool else
  0:u32 == dsa_R_EDX_32_1_6180:u32
dsa_R_PF_3_6187:bool =
  if dsa_T_origCOUNT_1_6179:u32 == 0:u32 then dsa_R_PF_1_6176:bool else
  ~low:bool(let dsa_T_acc_1_6185:u32 :=
                                         dsa_R_EDX_32_1_6180:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_6180:u32 in
            let dsa_T_acc_2_6186:u32 :=
                                         dsa_T_acc_1_6185:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6185:u32 in
            dsa_T_acc_2_6186:u32 >> 1:u32 ^ dsa_T_acc_2_6186:u32)
dsa_R_AF_1_6188:bool =
  if dsa_T_origCOUNT_1_6179:u32 == 0:u32 then dsa_R_AF_1_6175:bool else
  unknown "AF undefined after shift":bool
addr 0xdcf03212 @asm "lea    eax,[edx+edx*4]" @tid "0"
  @context "R_EAX_32" = 0xcccccccd, -1, u32, wr
  @context "R_EDX_32" = 0x0, -1, u32, rd
  @context "R_EDX_32" = 0x0, -1, u32, rd
label pc_0xdcf03212
dsa_R_EAX_32_1_6189:u32 =
  dsa_R_EDX_32_1_6180:u32 + (dsa_R_EDX_32_1_6180:u32 << 2:u32)
addr 0xdcf03215 @asm "add    eax,eax" @tid "0"
  @context "R_EAX_32" = 0x0, -1, u32, rw
  @context "R_EAX_32" = 0x0, -1, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
label pc_0xdcf03215
dsa_R_DF_1_6190:bool = false
dsa_T_t1_1_6191:u32 = dsa_R_EAX_32_1_6189:u32
dsa_T_t2_1_6192:u32 = dsa_R_EAX_32_1_6189:u32
dsa_R_EAX_32_1_6193:u32 = dsa_R_EAX_32_1_6189:u32 + dsa_T_t2_1_6192:u32
dsa_R_CF_1_6194:bool = dsa_R_EAX_32_1_6193:u32 < dsa_T_t1_1_6191:u32
dsa_R_OF_1_6195:bool =
  high:bool((dsa_T_t1_1_6191:u32 ^ ~dsa_T_t2_1_6192:u32) &
            (dsa_T_t1_1_6191:u32 ^ dsa_R_EAX_32_1_6193:u32))
dsa_R_AF_1_6196:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_6193:u32 ^ dsa_T_t1_1_6191:u32 ^ dsa_T_t2_1_6192:u32))
dsa_R_PF_3_6199:bool =
  ~low:bool(let dsa_T_acc_1_6197:u32 :=
                                         dsa_R_EAX_32_1_6193:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_6193:u32 in
            let dsa_T_acc_2_6198:u32 :=
                                         dsa_T_acc_1_6197:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6197:u32 in
            dsa_T_acc_2_6198:u32 >> 1:u32 ^ dsa_T_acc_2_6198:u32)
dsa_R_SF_1_6200:bool = high:bool(dsa_R_EAX_32_1_6193:u32)
dsa_R_ZF_1_6201:bool = 0:u32 == dsa_R_EAX_32_1_6193:u32
addr 0xdcf03217 @asm "sub    ecx,eax" @tid "0"
  @context "R_ECX_32" = 0x1, -1, u32, rw
  @context "R_EAX_32" = 0x0, -1, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
label pc_0xdcf03217
dsa_R_DF_1_6202:bool = false
dsa_T_t_1_6203:u32 = dsa_R_ECX_32_1_6141:u32
dsa_R_ECX_32_1_6204:u32 = dsa_R_ECX_32_1_6141:u32 - dsa_R_EAX_32_1_6193:u32
dsa_R_CF_1_6205:bool = dsa_T_t_1_6203:u32 < dsa_R_EAX_32_1_6193:u32
dsa_R_OF_1_6206:bool =
  high:bool((dsa_T_t_1_6203:u32 ^ dsa_R_EAX_32_1_6193:u32) &
            (dsa_T_t_1_6203:u32 ^ dsa_R_ECX_32_1_6204:u32))
dsa_R_AF_1_6207:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_6204:u32 ^ dsa_T_t_1_6203:u32 ^ dsa_R_EAX_32_1_6193:u32))
dsa_R_PF_3_6210:bool =
  ~low:bool(let dsa_T_acc_1_6208:u32 :=
                                         dsa_R_ECX_32_1_6204:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_6204:u32 in
            let dsa_T_acc_2_6209:u32 :=
                                         dsa_T_acc_1_6208:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6208:u32 in
            dsa_T_acc_2_6209:u32 >> 1:u32 ^ dsa_T_acc_2_6209:u32)
dsa_R_SF_1_6211:bool = high:bool(dsa_R_ECX_32_1_6204:u32)
dsa_R_ZF_1_6212:bool = 0:u32 == dsa_R_ECX_32_1_6204:u32
addr 0xdcf03219 @asm "test   edx,edx" @tid "0"
  @context "R_EDX_32" = 0x0, -1, u32, rd
  @context "R_EDX_32" = 0x0, -1, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcf03219
dsa_R_DF_1_6213:bool = false
dsa_T_t_1_6214:u32 = dsa_R_EDX_32_1_6180:u32 & dsa_R_EDX_32_1_6180:u32
dsa_R_OF_1_6215:bool = false
dsa_R_CF_1_6216:bool = false
dsa_R_AF_1_6217:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_6220:bool =
  ~low:bool(let dsa_T_acc_1_6218:u32 :=
                                         dsa_T_t_1_6214:u32 >> 4:u32 ^
                                         dsa_T_t_1_6214:u32 in
            let dsa_T_acc_2_6219:u32 :=
                                         dsa_T_acc_1_6218:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6218:u32 in
            dsa_T_acc_2_6219:u32 >> 1:u32 ^ dsa_T_acc_2_6219:u32)
dsa_R_SF_1_6221:bool = high:bool(dsa_T_t_1_6214:u32)
dsa_R_ZF_1_6222:bool = 0:u32 == dsa_T_t_1_6214:u32
addr 0xdcf0321b @asm "movzx  eax,BYTE PTR [edi+ecx*1]" @tid "0"
  @context "R_EAX_32" = 0x0, -1, u32, wr
  @context "R_EDI_32" = 0xdd01cc60, 0, u32, rd
  @context "R_ECX_32" = 0x1, -1, u32, rd
  @context "mem32[0xdd01cc61]" = 0x31, 0, u8, rd
label pc_0xdcf0321b
dsa_mem_dd01cc61_1_6223:u8 = low:u8(0x31:u8)
dsa_R_EDI_32_1_6224:u32 = 0xdd01cc60:u32
dsa_R_EAX_32_1_6225:u32 = pad:u32(pad:u8(dsa_mem_dd01cc61_1_6223:u8))
addr 0xdcf0321f @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x1, -1, u32, wr
  @context "R_EDX_32" = 0x0, -1, u32, rd
label pc_0xdcf0321f
dsa_R_ECX_32_1_6226:u32 = dsa_R_EDX_32_1_6180:u32
addr 0xdcf03221 @asm "mov    BYTE PTR [esi],al" @tid "0"
  @context "R_ESI_32" = 0xffaf0676, 0, u32, rd
  @context "R_EAX_32" = 0x31, -1, u32, rd
  @context "mem32[0xffaf0676]" = 0x31, -1, u8, wr
label pc_0xdcf03221
dsa_R_ESI_32_1_6227:u32 = 0xffaf0676:u32
dsa_mem_ffaf0676_1_6228:u8 = low:u8(low:u8(dsa_R_EAX_32_1_6225:u32))
addr 0xdcf03223 @asm "jne    0x00000000dcf03208" @tid "0"
  @context "R_EIP" = 0xdcf03223, 0, u32, rw
  @context "R_EFLAGS" = 0x246, -1, u32, rd
label pc_0xdcf03223
dsa_R_DF_1_6229:bool = false
dsa_R_EIP_1_6230:u32 = 0xdcf03223:u32
assert ~~dsa_R_ZF_1_6222:bool
/*Removed: cjmp ~R_ZF_662:bool, 0xdcf03208:u32, "nocjmp148"*/
label nocjmp148
addr 0xdcf03226 @asm "mov    eax,esi" @tid "0"
  @context "R_EAX_32" = 0x31, -1, u32, wr
  @context "R_ESI_32" = 0xffaf0676, 0, u32, rd
label pc_0xdcf03226
dsa_R_ESI_32_1_6231:u32 = 0xffaf0676:u32
dsa_R_EAX_32_1_6232:u32 = dsa_R_ESI_32_1_6231:u32
addr 0xdcf06929 @asm "cmp    DWORD PTR [ebp-0x484],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
  @context "mem32[0xffaf0214]" = 0xff, 0, u8, rd
  @context "mem32[0xffaf0215]" = 0xff, 0, u8, rd
  @context "mem32[0xffaf0216]" = 0xff, 0, u8, rd
  @context "mem32[0xffaf0217]" = 0xff, 0, u8, rd
label pc_0xdcf06929
dsa_mem_ffaf0216_1_6233:u8 = low:u8(-1:u8)
dsa_mem_ffaf0217_1_6234:u8 = low:u8(-1:u8)
dsa_mem_ffaf0215_1_6235:u8 = low:u8(-1:u8)
dsa_mem_ffaf0214_1_6236:u8 = low:u8(-1:u8)
dsa_R_EBP_32_1_6237:u32 = 0xffaf0698:u32
dsa_R_DF_1_6238:bool = false
dsa_T_t_1_6239:u32 =
  (pad:u32(dsa_mem_ffaf0217_1_6234:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf0216_1_6233:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf0215_1_6235:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf0214_1_6236:u8)))) - 0:u32
dsa_R_CF_1_6240:bool =
  (pad:u32(dsa_mem_ffaf0217_1_6234:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf0216_1_6233:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf0215_1_6235:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf0214_1_6236:u8)))) < 0:u32
dsa_R_OF_1_6241:bool =
  high:bool(((pad:u32(dsa_mem_ffaf0217_1_6234:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf0216_1_6233:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf0215_1_6235:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf0214_1_6236:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf0217_1_6234:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf0216_1_6233:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf0215_1_6235:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf0214_1_6236:u8)))) ^ dsa_T_t_1_6239:u32))
dsa_R_AF_1_6242:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6239:u32 ^
   (pad:u32(dsa_mem_ffaf0217_1_6234:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf0216_1_6233:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf0215_1_6235:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf0214_1_6236:u8)))) ^ 0:u32))
dsa_R_PF_3_6245:bool =
  ~low:bool(let dsa_T_acc_1_6243:u32 :=
                                         dsa_T_t_1_6239:u32 >> 4:u32 ^
                                         dsa_T_t_1_6239:u32 in
            let dsa_T_acc_2_6244:u32 :=
                                         dsa_T_acc_1_6243:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6243:u32 in
            dsa_T_acc_2_6244:u32 >> 1:u32 ^ dsa_T_acc_2_6244:u32)
dsa_R_SF_1_6246:bool = high:bool(dsa_T_t_1_6239:u32)
dsa_R_ZF_1_6247:bool = 0:u32 == dsa_T_t_1_6239:u32
addr 0xdcf03ec7 @asm "cmp    DWORD PTR [ebp-0x4b8],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x293, 0, u32, wr
  @context "mem32[0xffaf01e0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e3]" = 0x41, -1, u8, rd
label pc_0xdcf03ec7
dsa_R_ZF_1_6248:bool = false
dsa_R_EBP_32_1_6249:u32 = 0xffaf0698:u32
dsa_R_AF_1_6250:bool = true
dsa_R_OF_1_6251:bool = false
dsa_R_SF_1_6252:bool = true
dsa_R_DF_1_6253:bool = false
dsa_R_CF_1_6254:bool = true
dsa_R_EFLAGS_1_6255:u32 = 0x293:u32
dsa_R_PF_1_6256:bool = false
dsa_T_t_1_6257:u32 =
  (pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) - 0:u32
dsa_R_CF_1_6258:bool =
  (pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) < 0:u32
dsa_R_OF_1_6259:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) ^ dsa_T_t_1_6257:u32))
dsa_R_AF_1_6260:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6257:u32 ^
   (pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) ^ 0:u32))
dsa_R_PF_3_6263:bool =
  ~low:bool(let dsa_T_acc_1_6261:u32 :=
                                         dsa_T_t_1_6257:u32 >> 4:u32 ^
                                         dsa_T_t_1_6257:u32 in
            let dsa_T_acc_2_6262:u32 :=
                                         dsa_T_acc_1_6261:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6261:u32 in
            dsa_T_acc_2_6262:u32 >> 1:u32 ^ dsa_T_acc_2_6262:u32)
dsa_R_SF_1_6264:bool = high:bool(dsa_T_t_1_6257:u32)
dsa_R_ZF_1_6265:bool = 0:u32 == dsa_T_t_1_6257:u32
addr 0xdcf03ece @asm "je     0x00000000dcf03ef5" @tid "0"
  @context "R_EIP" = 0xdcf03ece, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcf03ece
dsa_R_DF_1_6266:bool = false
dsa_R_EIP_1_6267:u32 = 0xdcf03ece:u32
assert ~dsa_R_ZF_1_6265:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf03ef5:u32, "nocjmp149"*/
label nocjmp149
addr 0xdcf03ed0 @asm "cmp    DWORD PTR [ebp-0x4b0],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
  @context "mem32[0xffaf01e8]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e9]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01ea]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01eb]" = 0x0, 0, u8, rd
label pc_0xdcf03ed0
dsa_mem_ffaf01eb_1_6268:u8 = low:u8(0:u8)
dsa_mem_ffaf01e8_1_6269:u8 = low:u8(0:u8)
dsa_mem_ffaf01e9_1_6270:u8 = low:u8(0:u8)
dsa_mem_ffaf01ea_1_6271:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_6272:u32 = 0xffaf0698:u32
dsa_R_DF_1_6273:bool = false
dsa_T_t_1_6274:u32 =
  (pad:u32(dsa_mem_ffaf01eb_1_6268:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01ea_1_6271:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e9_1_6270:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e8_1_6269:u8)))) - 0:u32
dsa_R_CF_1_6275:bool =
  (pad:u32(dsa_mem_ffaf01eb_1_6268:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01ea_1_6271:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e9_1_6270:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e8_1_6269:u8)))) < 0:u32
dsa_R_OF_1_6276:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01eb_1_6268:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01ea_1_6271:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e9_1_6270:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e8_1_6269:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01eb_1_6268:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01ea_1_6271:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e9_1_6270:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e8_1_6269:u8)))) ^ dsa_T_t_1_6274:u32))
dsa_R_AF_1_6277:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6274:u32 ^
   (pad:u32(dsa_mem_ffaf01eb_1_6268:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01ea_1_6271:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e9_1_6270:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e8_1_6269:u8)))) ^ 0:u32))
dsa_R_PF_3_6280:bool =
  ~low:bool(let dsa_T_acc_1_6278:u32 :=
                                         dsa_T_t_1_6274:u32 >> 4:u32 ^
                                         dsa_T_t_1_6274:u32 in
            let dsa_T_acc_2_6279:u32 :=
                                         dsa_T_acc_1_6278:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6278:u32 in
            dsa_T_acc_2_6279:u32 >> 1:u32 ^ dsa_T_acc_2_6279:u32)
dsa_R_SF_1_6281:bool = high:bool(dsa_T_t_1_6274:u32)
dsa_R_ZF_1_6282:bool = 0:u32 == dsa_T_t_1_6274:u32
addr 0xdcf03efb @asm "mov    edx,DWORD PTR [ebp-0x49c]" @tid "0"
  @context "R_EDX_32" = 0x0, -1, u32, wr
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "mem32[0xffaf01fc]" = 0x1, 0, u8, rd
  @context "mem32[0xffaf01fd]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01fe]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01ff]" = 0x0, 0, u8, rd
label pc_0xdcf03efb
dsa_mem_ffaf01fe_1_6283:u8 = low:u8(0:u8)
dsa_mem_ffaf01fc_1_6284:u8 = low:u8(1:u8)
dsa_mem_ffaf01fd_1_6285:u8 = low:u8(0:u8)
dsa_mem_ffaf01ff_1_6286:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_6287:u32 = 0xffaf0698:u32
dsa_R_EDX_32_1_6288:u32 =
  pad:u32(dsa_mem_ffaf01ff_1_6286:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01fe_1_6283:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01fd_1_6285:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01fc_1_6284:u8)))
addr 0xdcf03f34 @asm "cmp    DWORD PTR [ebp-0x4b8],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
  @context "mem32[0xffaf01e0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e3]" = 0x41, -1, u8, rd
label pc_0xdcf03f34
dsa_R_ZF_1_6289:bool = false
dsa_R_EBP_32_1_6290:u32 = 0xffaf0698:u32
dsa_R_AF_1_6291:bool = false
dsa_R_OF_1_6292:bool = false
dsa_R_SF_1_6293:bool = true
dsa_R_DF_1_6294:bool = false
dsa_R_CF_1_6295:bool = false
dsa_R_EFLAGS_1_6296:u32 = 0x286:u32
dsa_R_PF_1_6297:bool = true
dsa_T_t_1_6298:u32 =
  (pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) - 0:u32
dsa_R_CF_1_6299:bool =
  (pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) < 0:u32
dsa_R_OF_1_6300:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) ^ dsa_T_t_1_6298:u32))
dsa_R_AF_1_6301:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6298:u32 ^
   (pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) ^ 0:u32))
dsa_R_PF_3_6304:bool =
  ~low:bool(let dsa_T_acc_1_6302:u32 :=
                                         dsa_T_t_1_6298:u32 >> 4:u32 ^
                                         dsa_T_t_1_6298:u32 in
            let dsa_T_acc_2_6303:u32 :=
                                         dsa_T_acc_1_6302:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6302:u32 in
            dsa_T_acc_2_6303:u32 >> 1:u32 ^ dsa_T_acc_2_6303:u32)
dsa_R_SF_1_6305:bool = high:bool(dsa_T_t_1_6298:u32)
dsa_R_ZF_1_6306:bool = 0:u32 == dsa_T_t_1_6298:u32
addr 0xdcf03f3b @asm "je     0x00000000dcf03f58" @tid "0"
  @context "R_EIP" = 0xdcf03f3b, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcf03f3b
dsa_R_DF_1_6307:bool = false
dsa_R_EIP_1_6308:u32 = 0xdcf03f3b:u32
assert ~dsa_R_ZF_1_6306:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf03f58:u32, "nocjmp150"*/
label nocjmp150
addr 0xdcf03f3d @asm "cmp    DWORD PTR [ebp-0x4b0],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
  @context "mem32[0xffaf01e8]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e9]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01ea]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01eb]" = 0x0, 0, u8, rd
label pc_0xdcf03f3d
dsa_mem_ffaf01eb_1_6309:u8 = low:u8(0:u8)
dsa_mem_ffaf01e8_1_6310:u8 = low:u8(0:u8)
dsa_mem_ffaf01e9_1_6311:u8 = low:u8(0:u8)
dsa_mem_ffaf01ea_1_6312:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_6313:u32 = 0xffaf0698:u32
dsa_R_DF_1_6314:bool = false
dsa_T_t_1_6315:u32 =
  (pad:u32(dsa_mem_ffaf01eb_1_6309:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01ea_1_6312:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e9_1_6311:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e8_1_6310:u8)))) - 0:u32
dsa_R_CF_1_6316:bool =
  (pad:u32(dsa_mem_ffaf01eb_1_6309:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01ea_1_6312:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e9_1_6311:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e8_1_6310:u8)))) < 0:u32
dsa_R_OF_1_6317:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01eb_1_6309:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01ea_1_6312:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e9_1_6311:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e8_1_6310:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01eb_1_6309:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01ea_1_6312:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e9_1_6311:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e8_1_6310:u8)))) ^ dsa_T_t_1_6315:u32))
dsa_R_AF_1_6318:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6315:u32 ^
   (pad:u32(dsa_mem_ffaf01eb_1_6309:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01ea_1_6312:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e9_1_6311:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e8_1_6310:u8)))) ^ 0:u32))
dsa_R_PF_3_6321:bool =
  ~low:bool(let dsa_T_acc_1_6319:u32 :=
                                         dsa_T_t_1_6315:u32 >> 4:u32 ^
                                         dsa_T_t_1_6315:u32 in
            let dsa_T_acc_2_6320:u32 :=
                                         dsa_T_acc_1_6319:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6319:u32 in
            dsa_T_acc_2_6320:u32 >> 1:u32 ^ dsa_T_acc_2_6320:u32)
dsa_R_SF_1_6322:bool = high:bool(dsa_T_t_1_6315:u32)
dsa_R_ZF_1_6323:bool = 0:u32 == dsa_T_t_1_6315:u32
addr 0xdcf03f5e @asm "or     eax,DWORD PTR [ebp-0x4bc]" @tid "0"
  @context "R_EAX_32" = 0x0, 0, u32, rw
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, 0, u32, wr
  @context "mem32[0xffaf01dc]" = 0x0, -1, u8, rd
  @context "mem32[0xffaf01dd]" = 0x0, -1, u8, rd
  @context "mem32[0xffaf01de]" = 0x0, -1, u8, rd
  @context "mem32[0xffaf01df]" = 0x0, -1, u8, rd
label pc_0xdcf03f5e
dsa_R_ZF_1_6324:bool = true
dsa_R_EBP_32_1_6325:u32 = 0xffaf0698:u32
dsa_R_AF_1_6326:bool = false
dsa_R_OF_1_6327:bool = false
dsa_R_SF_1_6328:bool = false
dsa_R_DF_1_6329:bool = false
dsa_R_EAX_32_1_6330:u32 = 0:u32
dsa_R_CF_1_6331:bool = false
dsa_R_EFLAGS_1_6332:u32 = 0x246:u32
dsa_R_PF_1_6333:bool = true
dsa_R_EAX_32_1_6334:u32 =
  dsa_R_EAX_32_1_6330:u32 |
  (pad:u32(dsa_mem_ffaf01df_1_5332:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01de_1_5331:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01dd_1_5330:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01dc_1_5329:u8))))
dsa_R_OF_1_6335:bool = false
dsa_R_CF_1_6336:bool = false
dsa_R_AF_1_6337:bool = unknown "AF is undefined after or":bool
dsa_R_PF_3_6340:bool =
  ~low:bool(let dsa_T_acc_1_6338:u32 :=
                                         dsa_R_EAX_32_1_6334:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_6334:u32 in
            let dsa_T_acc_2_6339:u32 :=
                                         dsa_T_acc_1_6338:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6338:u32 in
            dsa_T_acc_2_6339:u32 >> 1:u32 ^ dsa_T_acc_2_6339:u32)
dsa_R_SF_1_6341:bool = high:bool(dsa_R_EAX_32_1_6334:u32)
dsa_R_ZF_1_6342:bool = 0:u32 == dsa_R_EAX_32_1_6334:u32
addr 0xdcf03f64 @asm "or     eax,DWORD PTR [ebp-0x4b4]" @tid "0"
  @context "R_EAX_32" = 0x0, -1, u32, rw
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
  @context "mem32[0xffaf01e4]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e5]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e6]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e7]" = 0x0, 0, u8, rd
label pc_0xdcf03f64
dsa_mem_ffaf01e4_1_6343:u8 = low:u8(0:u8)
dsa_mem_ffaf01e5_1_6344:u8 = low:u8(0:u8)
dsa_mem_ffaf01e7_1_6345:u8 = low:u8(0:u8)
dsa_mem_ffaf01e6_1_6346:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_6347:u32 = 0xffaf0698:u32
dsa_R_DF_1_6348:bool = false
dsa_R_EAX_32_1_6349:u32 =
  dsa_R_EAX_32_1_6334:u32 |
  (pad:u32(dsa_mem_ffaf01e7_1_6345:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e6_1_6346:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e5_1_6344:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e4_1_6343:u8))))
dsa_R_OF_1_6350:bool = false
dsa_R_CF_1_6351:bool = false
dsa_R_AF_1_6352:bool = unknown "AF is undefined after or":bool
dsa_R_PF_3_6355:bool =
  ~low:bool(let dsa_T_acc_1_6353:u32 :=
                                         dsa_R_EAX_32_1_6349:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_6349:u32 in
            let dsa_T_acc_2_6354:u32 :=
                                         dsa_T_acc_1_6353:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6353:u32 in
            dsa_T_acc_2_6354:u32 >> 1:u32 ^ dsa_T_acc_2_6354:u32)
dsa_R_SF_1_6356:bool = high:bool(dsa_R_EAX_32_1_6349:u32)
dsa_R_ZF_1_6357:bool = 0:u32 == dsa_R_EAX_32_1_6349:u32
addr 0xdcf03f6a @asm "cmp    eax,0x1" @tid "0"
  @context "R_EAX_32" = 0x0, -1, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
label pc_0xdcf03f6a
dsa_R_DF_1_6358:bool = false
dsa_T_t_1_6359:u32 = dsa_R_EAX_32_1_6349:u32 - 1:u32
dsa_R_CF_1_6360:bool = dsa_R_EAX_32_1_6349:u32 < 1:u32
dsa_R_OF_1_6361:bool =
  high:bool((dsa_R_EAX_32_1_6349:u32 ^ 1:u32) &
            (dsa_R_EAX_32_1_6349:u32 ^ dsa_T_t_1_6359:u32))
dsa_R_AF_1_6362:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_T_t_1_6359:u32 ^ dsa_R_EAX_32_1_6349:u32 ^ 1:u32))
dsa_R_PF_3_6365:bool =
  ~low:bool(let dsa_T_acc_1_6363:u32 :=
                                         dsa_T_t_1_6359:u32 >> 4:u32 ^
                                         dsa_T_t_1_6359:u32 in
            let dsa_T_acc_2_6364:u32 :=
                                         dsa_T_acc_1_6363:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6363:u32 in
            dsa_T_acc_2_6364:u32 >> 1:u32 ^ dsa_T_acc_2_6364:u32)
dsa_R_SF_1_6366:bool = high:bool(dsa_T_t_1_6359:u32)
dsa_R_ZF_1_6367:bool = 0:u32 == dsa_T_t_1_6359:u32
addr 0xdcf03f6d @asm "adc    edx,0xffffffff" @tid "0"
  @context "R_EDX_32" = 0xfffffff6, 0, u32, rw
  @context "R_EFLAGS" = 0x297, -1, u32, rw
label pc_0xdcf03f6d
dsa_R_DF_1_6368:bool = false
dsa_R_EDX_32_1_6369:u32 = 0xfffffff6:u32
dsa_T_orig1_1_6370:u32 = dsa_R_EDX_32_1_6369:u32
dsa_T_orig2_1_6371:u32 = -1:u32
dsa_R_EDX_32_1_6372:u32 =
  dsa_T_orig1_1_6370:u32 + dsa_T_orig2_1_6371:u32 +
  pad:u32(dsa_R_CF_1_6360:bool)
dsa_R_CF_1_6373:bool =
  extract:32:32:[pad:u33(dsa_T_orig1_1_6370:u32) +
                 pad:u33(dsa_T_orig2_1_6371:u32) +
                 pad:u33(dsa_R_CF_1_6360:bool)]
dsa_R_OF_1_6374:bool =
  high:bool((dsa_T_orig1_1_6370:u32 ^ ~dsa_T_orig2_1_6371:u32) &
            (dsa_T_orig1_1_6370:u32 ^ dsa_R_EDX_32_1_6372:u32))
dsa_R_AF_1_6375:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EDX_32_1_6372:u32 ^ dsa_T_orig1_1_6370:u32 ^ dsa_T_orig2_1_6371:u32))
dsa_R_PF_3_6378:bool =
  ~low:bool(let dsa_T_acc_1_6376:u32 :=
                                         dsa_R_EDX_32_1_6372:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_6372:u32 in
            let dsa_T_acc_2_6377:u32 :=
                                         dsa_T_acc_1_6376:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6376:u32 in
            dsa_T_acc_2_6377:u32 >> 1:u32 ^ dsa_T_acc_2_6377:u32)
dsa_R_SF_1_6379:bool = high:bool(dsa_R_EDX_32_1_6372:u32)
dsa_R_ZF_1_6380:bool = 0:u32 == dsa_R_EDX_32_1_6372:u32
addr 0xdcf03f7d @asm "cmp    DWORD PTR [ebp-0x4bc],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, 0, u32, wr
  @context "mem32[0xffaf01dc]" = 0x0, -1, u8, rd
  @context "mem32[0xffaf01dd]" = 0x0, -1, u8, rd
  @context "mem32[0xffaf01de]" = 0x0, -1, u8, rd
  @context "mem32[0xffaf01df]" = 0x0, -1, u8, rd
label pc_0xdcf03f7d
dsa_R_ZF_1_6381:bool = true
dsa_R_EBP_32_1_6382:u32 = 0xffaf0698:u32
dsa_R_AF_1_6383:bool = false
dsa_R_OF_1_6384:bool = false
dsa_R_SF_1_6385:bool = false
dsa_R_DF_1_6386:bool = false
dsa_R_CF_1_6387:bool = false
dsa_R_EFLAGS_1_6388:u32 = 0x246:u32
dsa_R_PF_1_6389:bool = true
dsa_T_t_1_6390:u32 =
  (pad:u32(dsa_mem_ffaf01df_1_5332:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01de_1_5331:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01dd_1_5330:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01dc_1_5329:u8)))) - 0:u32
dsa_R_CF_1_6391:bool =
  (pad:u32(dsa_mem_ffaf01df_1_5332:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01de_1_5331:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01dd_1_5330:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01dc_1_5329:u8)))) < 0:u32
dsa_R_OF_1_6392:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01df_1_5332:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01de_1_5331:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01dd_1_5330:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01dc_1_5329:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01df_1_5332:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01de_1_5331:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01dd_1_5330:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01dc_1_5329:u8)))) ^ dsa_T_t_1_6390:u32))
dsa_R_AF_1_6393:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6390:u32 ^
   (pad:u32(dsa_mem_ffaf01df_1_5332:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01de_1_5331:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01dd_1_5330:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01dc_1_5329:u8)))) ^ 0:u32))
dsa_R_PF_3_6396:bool =
  ~low:bool(let dsa_T_acc_1_6394:u32 :=
                                         dsa_T_t_1_6390:u32 >> 4:u32 ^
                                         dsa_T_t_1_6390:u32 in
            let dsa_T_acc_2_6395:u32 :=
                                         dsa_T_acc_1_6394:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6394:u32 in
            dsa_T_acc_2_6395:u32 >> 1:u32 ^ dsa_T_acc_2_6395:u32)
dsa_R_SF_1_6397:bool = high:bool(dsa_T_t_1_6390:u32)
dsa_R_ZF_1_6398:bool = 0:u32 == dsa_T_t_1_6390:u32
addr 0xdcf03f84 @asm "je     0x00000000dcf06677" @tid "0"
  @context "R_EIP" = 0xdcf03f84, 0, u32, rw
  @context "R_EFLAGS" = 0x246, -1, u32, rd
label pc_0xdcf03f84
dsa_R_DF_1_6399:bool = false
dsa_R_EIP_1_6400:u32 = 0xdcf03f84:u32
assert dsa_R_ZF_1_6398:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf06677:u32, "nocjmp151"*/
addr 0xdcf06677 @asm "cmp    DWORD PTR [ebp-0x4b4],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, -1, u32, wr
  @context "mem32[0xffaf01e4]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e5]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e6]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e7]" = 0x0, 0, u8, rd
label pc_0xdcf06677
dsa_mem_ffaf01e4_1_6401:u8 = low:u8(0:u8)
dsa_mem_ffaf01e5_1_6402:u8 = low:u8(0:u8)
dsa_mem_ffaf01e7_1_6403:u8 = low:u8(0:u8)
dsa_mem_ffaf01e6_1_6404:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_6405:u32 = 0xffaf0698:u32
dsa_R_DF_1_6406:bool = false
dsa_T_t_1_6407:u32 =
  (pad:u32(dsa_mem_ffaf01e7_1_6403:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e6_1_6404:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e5_1_6402:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e4_1_6401:u8)))) - 0:u32
dsa_R_CF_1_6408:bool =
  (pad:u32(dsa_mem_ffaf01e7_1_6403:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e6_1_6404:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e5_1_6402:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e4_1_6401:u8)))) < 0:u32
dsa_R_OF_1_6409:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01e7_1_6403:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e6_1_6404:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e5_1_6402:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e4_1_6401:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01e7_1_6403:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e6_1_6404:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e5_1_6402:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e4_1_6401:u8)))) ^ dsa_T_t_1_6407:u32))
dsa_R_AF_1_6410:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6407:u32 ^
   (pad:u32(dsa_mem_ffaf01e7_1_6403:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01e6_1_6404:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e5_1_6402:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e4_1_6401:u8)))) ^ 0:u32))
dsa_R_PF_3_6413:bool =
  ~low:bool(let dsa_T_acc_1_6411:u32 :=
                                         dsa_T_t_1_6407:u32 >> 4:u32 ^
                                         dsa_T_t_1_6407:u32 in
            let dsa_T_acc_2_6412:u32 :=
                                         dsa_T_acc_1_6411:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6411:u32 in
            dsa_T_acc_2_6412:u32 >> 1:u32 ^ dsa_T_acc_2_6412:u32)
dsa_R_SF_1_6414:bool = high:bool(dsa_T_t_1_6407:u32)
dsa_R_ZF_1_6415:bool = 0:u32 == dsa_T_t_1_6407:u32
addr 0xdcf03fb6 @asm "cmp    DWORD PTR [ebp-0x4b8],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x246, 0, u32, wr
  @context "mem32[0xffaf01e0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf01e3]" = 0x41, -1, u8, rd
label pc_0xdcf03fb6
dsa_R_ZF_1_6416:bool = true
dsa_R_EBP_32_1_6417:u32 = 0xffaf0698:u32
dsa_R_AF_1_6418:bool = false
dsa_R_OF_1_6419:bool = false
dsa_R_SF_1_6420:bool = false
dsa_R_DF_1_6421:bool = false
dsa_R_CF_1_6422:bool = false
dsa_R_EFLAGS_1_6423:u32 = 0x246:u32
dsa_R_PF_1_6424:bool = true
dsa_T_t_1_6425:u32 =
  (pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) - 0:u32
dsa_R_CF_1_6426:bool =
  (pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) < 0:u32
dsa_R_OF_1_6427:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) ^ dsa_T_t_1_6425:u32))
dsa_R_AF_1_6428:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6425:u32 ^
   (pad:u32(dsa_mem_ffaf01e3_1_5341:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01e2_1_5340:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e1_1_5339:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e0_1_5338:u8)))) ^ 0:u32))
dsa_R_PF_3_6431:bool =
  ~low:bool(let dsa_T_acc_1_6429:u32 :=
                                         dsa_T_t_1_6425:u32 >> 4:u32 ^
                                         dsa_T_t_1_6425:u32 in
            let dsa_T_acc_2_6430:u32 :=
                                         dsa_T_acc_1_6429:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6429:u32 in
            dsa_T_acc_2_6430:u32 >> 1:u32 ^ dsa_T_acc_2_6430:u32)
dsa_R_SF_1_6432:bool = high:bool(dsa_T_t_1_6425:u32)
dsa_R_ZF_1_6433:bool = 0:u32 == dsa_T_t_1_6425:u32
addr 0xdcf03fbd @asm "je     0x00000000dcf04028" @tid "0"
  @context "R_EIP" = 0xdcf03fbd, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcf03fbd
dsa_R_DF_1_6434:bool = false
dsa_R_EIP_1_6435:u32 = 0xdcf03fbd:u32
assert ~dsa_R_ZF_1_6433:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf04028:u32, "nocjmp152"*/
label nocjmp152
addr 0xdcf03fbf @asm "cmp    DWORD PTR [ebp-0x4b0],0x0" @tid "0"
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "R_EFLAGS" = 0x206, -1, u32, wr
  @context "mem32[0xffaf01e8]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01e9]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01ea]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf01eb]" = 0x0, 0, u8, rd
label pc_0xdcf03fbf
dsa_mem_ffaf01eb_1_6436:u8 = low:u8(0:u8)
dsa_mem_ffaf01e8_1_6437:u8 = low:u8(0:u8)
dsa_mem_ffaf01e9_1_6438:u8 = low:u8(0:u8)
dsa_mem_ffaf01ea_1_6439:u8 = low:u8(0:u8)
dsa_R_EBP_32_1_6440:u32 = 0xffaf0698:u32
dsa_R_DF_1_6441:bool = false
dsa_T_t_1_6442:u32 =
  (pad:u32(dsa_mem_ffaf01eb_1_6436:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01ea_1_6439:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e9_1_6438:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e8_1_6437:u8)))) - 0:u32
dsa_R_CF_1_6443:bool =
  (pad:u32(dsa_mem_ffaf01eb_1_6436:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf01ea_1_6439:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf01e9_1_6438:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf01e8_1_6437:u8)))) < 0:u32
dsa_R_OF_1_6444:bool =
  high:bool(((pad:u32(dsa_mem_ffaf01eb_1_6436:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01ea_1_6439:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e9_1_6438:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e8_1_6437:u8)))) ^ 0:u32) &
            ((pad:u32(dsa_mem_ffaf01eb_1_6436:u8) << 0x18:u32 |
             (pad:u32(dsa_mem_ffaf01ea_1_6439:u8) << 0x10:u32 |
             (pad:u32(dsa_mem_ffaf01e9_1_6438:u8) << 8:u32 |
             pad:u32(dsa_mem_ffaf01e8_1_6437:u8)))) ^ dsa_T_t_1_6442:u32))
dsa_R_AF_1_6445:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6442:u32 ^
   (pad:u32(dsa_mem_ffaf01eb_1_6436:u8) << 0x18:u32 |
   (pad:u32(dsa_mem_ffaf01ea_1_6439:u8) << 0x10:u32 |
   (pad:u32(dsa_mem_ffaf01e9_1_6438:u8) << 8:u32 |
   pad:u32(dsa_mem_ffaf01e8_1_6437:u8)))) ^ 0:u32))
dsa_R_PF_3_6448:bool =
  ~low:bool(let dsa_T_acc_1_6446:u32 :=
                                         dsa_T_t_1_6442:u32 >> 4:u32 ^
                                         dsa_T_t_1_6442:u32 in
            let dsa_T_acc_2_6447:u32 :=
                                         dsa_T_acc_1_6446:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6446:u32 in
            dsa_T_acc_2_6447:u32 >> 1:u32 ^ dsa_T_acc_2_6447:u32)
dsa_R_SF_1_6449:bool = high:bool(dsa_T_t_1_6442:u32)
dsa_R_ZF_1_6450:bool = 0:u32 == dsa_T_t_1_6442:u32
addr 0xdcf0408a @asm "movsx  eax,BYTE PTR [esi+0x46]" @tid "0"
  @context "R_EAX_32" = 0x0, -1, u32, wr
  @context "R_ESI_32" = 0xdd06dac0, 0, u32, rd
  @context "mem32[0xdd06db06]" = 0x0, 0, u8, rd
label pc_0xdcf0408a
dsa_mem_dd06db06_1_6451:u8 = low:u8(0:u8)
dsa_R_ESI_32_1_6452:u32 = 0xdd06dac0:u32
dsa_R_EAX_32_1_6453:u32 = extend:u32(pad:u8(dsa_mem_dd06db06_1_6451:u8))
addr 0xdcf0408e @asm "mov    ecx,DWORD PTR [ebp-0x478]" @tid "0"
  @context "R_ECX_32" = 0x0, -1, u32, wr
  @context "R_EBP_32" = 0xffaf0698, 0, u32, rd
  @context "mem32[0xffaf0220]" = 0x76, 0, u8, rd
  @context "mem32[0xffaf0221]" = 0x6, 0, u8, rd
  @context "mem32[0xffaf0222]" = 0xaf, 0, u8, rd
  @context "mem32[0xffaf0223]" = 0xff, 0, u8, rd
label pc_0xdcf0408e
dsa_mem_ffaf0220_1_6454:u8 = low:u8(0x76:u8)
dsa_mem_ffaf0223_1_6455:u8 = low:u8(-1:u8)
dsa_mem_ffaf0222_1_6456:u8 = low:u8(0xaf:u8)
dsa_mem_ffaf0221_1_6457:u8 = low:u8(6:u8)
dsa_R_EBP_32_1_6458:u32 = 0xffaf0698:u32
dsa_R_ECX_32_1_6459:u32 =
  pad:u32(dsa_mem_ffaf0223_1_6455:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf0222_1_6456:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf0221_1_6457:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf0220_1_6454:u8)))
addr 0xdcf040a5 @asm "mov    DWORD PTR [esp],esi" @tid "0"
  @context "R_ESP_32" = 0xffaf0180, 0, u32, rd
  @context "R_ESI_32" = 0xdd06dac0, 0, u32, rd
  @context "mem32[0xffaf0180]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf0181]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf0182]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf0183]" = 0x41, -1, u8, wr
label pc_0xdcf040a5
dsa_R_ESI_32_1_6460:u32 = 0xdd06dac0:u32
dsa_R_ESP_32_1_6461:u32 = 0xffaf0180:u32
dsa_mem_ffaf0180_1_6462:u8 = low:u8(dsa_R_ESI_32_1_6460:u32)
dsa_mem_ffaf0181_1_6463:u8 = low:u8(dsa_R_ESI_32_1_6460:u32 >> 8:u32)
dsa_mem_ffaf0182_1_6464:u8 = low:u8(dsa_R_ESI_32_1_6460:u32 >> 0x10:u32)
dsa_mem_ffaf0183_1_6465:u8 = low:u8(dsa_R_ESI_32_1_6460:u32 >> 0x18:u32)
addr 0xdcf2f378 @asm "cmp    BYTE PTR [ebp-0x1],0xa" @tid "0"
  @context "R_EBP_32" = 0xffaf0680, 0, u32, rd
  @context "R_EFLAGS" = 0x287, 0, u32, wr
  @context "mem32[0xffaf067f]" = 0x35, -1, u8, rd
label pc_0xdcf2f378
dsa_R_ZF_1_6466:bool = false
dsa_R_EBP_32_1_6467:u32 = 0xffaf0680:u32
dsa_R_AF_1_6468:bool = false
dsa_R_OF_1_6469:bool = false
dsa_R_SF_1_6470:bool = true
dsa_R_DF_1_6471:bool = false
dsa_R_CF_1_6472:bool = true
dsa_R_EFLAGS_1_6473:u32 = 0x287:u32
dsa_R_PF_1_6474:bool = true
dsa_T_t_1_6475:u8 = pad:u8(dsa_mem_ffaf067f_1_5463:u8) - 0xa:u8
dsa_R_CF_1_6476:bool = pad:u8(dsa_mem_ffaf067f_1_5463:u8) < 0xa:u8
dsa_R_OF_1_6477:bool =
  high:bool((pad:u8(dsa_mem_ffaf067f_1_5463:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf067f_1_5463:u8) ^ dsa_T_t_1_6475:u8))
dsa_R_AF_1_6478:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_6475:u8 ^ pad:u8(dsa_mem_ffaf067f_1_5463:u8) ^ 0xa:u8))
dsa_R_PF_3_6481:bool =
  ~low:bool(let dsa_T_acc_1_6479:u8 :=
                                        dsa_T_t_1_6475:u8 >> 4:u8 ^
                                        dsa_T_t_1_6475:u8 in
            let dsa_T_acc_2_6480:u8 :=
                                        dsa_T_acc_1_6479:u8 >> 2:u8 ^
                                        dsa_T_acc_1_6479:u8 in
            dsa_T_acc_2_6480:u8 >> 1:u8 ^ dsa_T_acc_2_6480:u8)
dsa_R_SF_1_6482:bool = high:bool(dsa_T_t_1_6475:u8)
dsa_R_ZF_1_6483:bool = 0:u8 == dsa_T_t_1_6475:u8
addr 0xdcf2f37f @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f37f, 0, u32, rw
  @context "R_EFLAGS" = 0x216, -1, u32, rd
label pc_0xdcf2f37f
dsa_R_DF_1_6484:bool = false
dsa_R_EIP_1_6485:u32 = 0xdcf2f37f:u32
assert ~dsa_R_ZF_1_6483:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp153"*/
label nocjmp153
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf067f, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_6486:u32 = 0xffaf0676:u32
dsa_R_DF_1_6487:bool = false
dsa_R_EDX_32_1_6488:u32 = 0xffaf067f:u32
dsa_T_t_1_6489:u32 = dsa_R_EDX_32_1_6488:u32 - dsa_R_EBP_32_1_6486:u32
dsa_R_CF_1_6490:bool = dsa_R_EDX_32_1_6488:u32 < dsa_R_EBP_32_1_6486:u32
dsa_R_OF_1_6491:bool =
  high:bool((dsa_R_EDX_32_1_6488:u32 ^ dsa_R_EBP_32_1_6486:u32) &
            (dsa_R_EDX_32_1_6488:u32 ^ dsa_T_t_1_6489:u32))
dsa_R_AF_1_6492:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6489:u32 ^ dsa_R_EDX_32_1_6488:u32 ^ dsa_R_EBP_32_1_6486:u32))
dsa_R_PF_3_6495:bool =
  ~low:bool(let dsa_T_acc_1_6493:u32 :=
                                         dsa_T_t_1_6489:u32 >> 4:u32 ^
                                         dsa_T_t_1_6489:u32 in
            let dsa_T_acc_2_6494:u32 :=
                                         dsa_T_acc_1_6493:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6493:u32 in
            dsa_T_acc_2_6494:u32 >> 1:u32 ^ dsa_T_acc_2_6494:u32)
dsa_R_SF_1_6496:bool = high:bool(dsa_T_t_1_6489:u32)
dsa_R_ZF_1_6497:bool = 0:u32 == dsa_T_t_1_6489:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf067e, 0, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
  @context "mem32[0xffaf067e]" = 0x38, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_6498:bool = false
dsa_R_AF_1_6499:bool = false
dsa_R_OF_1_6500:bool = false
dsa_R_SF_1_6501:bool = true
dsa_R_DF_1_6502:bool = false
dsa_R_EDX_32_1_6503:u32 = 0xffaf067e:u32
dsa_R_CF_1_6504:bool = false
dsa_R_EFLAGS_1_6505:u32 = 0x286:u32
dsa_R_PF_1_6506:bool = true
dsa_T_t_1_6507:u8 = pad:u8(dsa_mem_ffaf067e_1_5548:u8) - 0xa:u8
dsa_R_CF_1_6508:bool = pad:u8(dsa_mem_ffaf067e_1_5548:u8) < 0xa:u8
dsa_R_OF_1_6509:bool =
  high:bool((pad:u8(dsa_mem_ffaf067e_1_5548:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf067e_1_5548:u8) ^ dsa_T_t_1_6507:u8))
dsa_R_AF_1_6510:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_6507:u8 ^ pad:u8(dsa_mem_ffaf067e_1_5548:u8) ^ 0xa:u8))
dsa_R_PF_3_6513:bool =
  ~low:bool(let dsa_T_acc_1_6511:u8 :=
                                        dsa_T_t_1_6507:u8 >> 4:u8 ^
                                        dsa_T_t_1_6507:u8 in
            let dsa_T_acc_2_6512:u8 :=
                                        dsa_T_acc_1_6511:u8 >> 2:u8 ^
                                        dsa_T_acc_1_6511:u8 in
            dsa_T_acc_2_6512:u8 >> 1:u8 ^ dsa_T_acc_2_6512:u8)
dsa_R_SF_1_6514:bool = high:bool(dsa_T_t_1_6507:u8)
dsa_R_ZF_1_6515:bool = 0:u8 == dsa_T_t_1_6507:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x216, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_6516:bool = false
dsa_R_EIP_1_6517:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_6515:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp154"*/
label nocjmp154
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf067e, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_6518:u32 = 0xffaf0676:u32
dsa_R_DF_1_6519:bool = false
dsa_R_EDX_32_1_6520:u32 = 0xffaf067e:u32
dsa_T_t_1_6521:u32 = dsa_R_EDX_32_1_6520:u32 - dsa_R_EBP_32_1_6518:u32
dsa_R_CF_1_6522:bool = dsa_R_EDX_32_1_6520:u32 < dsa_R_EBP_32_1_6518:u32
dsa_R_OF_1_6523:bool =
  high:bool((dsa_R_EDX_32_1_6520:u32 ^ dsa_R_EBP_32_1_6518:u32) &
            (dsa_R_EDX_32_1_6520:u32 ^ dsa_T_t_1_6521:u32))
dsa_R_AF_1_6524:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6521:u32 ^ dsa_R_EDX_32_1_6520:u32 ^ dsa_R_EBP_32_1_6518:u32))
dsa_R_PF_3_6527:bool =
  ~low:bool(let dsa_T_acc_1_6525:u32 :=
                                         dsa_T_t_1_6521:u32 >> 4:u32 ^
                                         dsa_T_t_1_6521:u32 in
            let dsa_T_acc_2_6526:u32 :=
                                         dsa_T_acc_1_6525:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6525:u32 in
            dsa_T_acc_2_6526:u32 >> 1:u32 ^ dsa_T_acc_2_6526:u32)
dsa_R_SF_1_6528:bool = high:bool(dsa_T_t_1_6521:u32)
dsa_R_ZF_1_6529:bool = 0:u32 == dsa_T_t_1_6521:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf067d, 0, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
  @context "mem32[0xffaf067d]" = 0x35, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_6530:bool = false
dsa_R_AF_1_6531:bool = false
dsa_R_OF_1_6532:bool = false
dsa_R_SF_1_6533:bool = true
dsa_R_DF_1_6534:bool = false
dsa_R_EDX_32_1_6535:u32 = 0xffaf067d:u32
dsa_R_CF_1_6536:bool = false
dsa_R_EFLAGS_1_6537:u32 = 0x286:u32
dsa_R_PF_1_6538:bool = true
dsa_T_t_1_6539:u8 = pad:u8(dsa_mem_ffaf067d_1_5633:u8) - 0xa:u8
dsa_R_CF_1_6540:bool = pad:u8(dsa_mem_ffaf067d_1_5633:u8) < 0xa:u8
dsa_R_OF_1_6541:bool =
  high:bool((pad:u8(dsa_mem_ffaf067d_1_5633:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf067d_1_5633:u8) ^ dsa_T_t_1_6539:u8))
dsa_R_AF_1_6542:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_6539:u8 ^ pad:u8(dsa_mem_ffaf067d_1_5633:u8) ^ 0xa:u8))
dsa_R_PF_3_6545:bool =
  ~low:bool(let dsa_T_acc_1_6543:u8 :=
                                        dsa_T_t_1_6539:u8 >> 4:u8 ^
                                        dsa_T_t_1_6539:u8 in
            let dsa_T_acc_2_6544:u8 :=
                                        dsa_T_acc_1_6543:u8 >> 2:u8 ^
                                        dsa_T_acc_1_6543:u8 in
            dsa_T_acc_2_6544:u8 >> 1:u8 ^ dsa_T_acc_2_6544:u8)
dsa_R_SF_1_6546:bool = high:bool(dsa_T_t_1_6539:u8)
dsa_R_ZF_1_6547:bool = 0:u8 == dsa_T_t_1_6539:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x216, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_6548:bool = false
dsa_R_EIP_1_6549:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_6547:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp155"*/
label nocjmp155
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf067d, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_6550:u32 = 0xffaf0676:u32
dsa_R_DF_1_6551:bool = false
dsa_R_EDX_32_1_6552:u32 = 0xffaf067d:u32
dsa_T_t_1_6553:u32 = dsa_R_EDX_32_1_6552:u32 - dsa_R_EBP_32_1_6550:u32
dsa_R_CF_1_6554:bool = dsa_R_EDX_32_1_6552:u32 < dsa_R_EBP_32_1_6550:u32
dsa_R_OF_1_6555:bool =
  high:bool((dsa_R_EDX_32_1_6552:u32 ^ dsa_R_EBP_32_1_6550:u32) &
            (dsa_R_EDX_32_1_6552:u32 ^ dsa_T_t_1_6553:u32))
dsa_R_AF_1_6556:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6553:u32 ^ dsa_R_EDX_32_1_6552:u32 ^ dsa_R_EBP_32_1_6550:u32))
dsa_R_PF_3_6559:bool =
  ~low:bool(let dsa_T_acc_1_6557:u32 :=
                                         dsa_T_t_1_6553:u32 >> 4:u32 ^
                                         dsa_T_t_1_6553:u32 in
            let dsa_T_acc_2_6558:u32 :=
                                         dsa_T_acc_1_6557:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6557:u32 in
            dsa_T_acc_2_6558:u32 >> 1:u32 ^ dsa_T_acc_2_6558:u32)
dsa_R_SF_1_6560:bool = high:bool(dsa_T_t_1_6553:u32)
dsa_R_ZF_1_6561:bool = 0:u32 == dsa_T_t_1_6553:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf067c, 0, u32, rd
  @context "R_EFLAGS" = 0x282, 0, u32, wr
  @context "mem32[0xffaf067c]" = 0x35, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_6562:bool = false
dsa_R_AF_1_6563:bool = false
dsa_R_OF_1_6564:bool = false
dsa_R_SF_1_6565:bool = true
dsa_R_DF_1_6566:bool = false
dsa_R_EDX_32_1_6567:u32 = 0xffaf067c:u32
dsa_R_CF_1_6568:bool = false
dsa_R_EFLAGS_1_6569:u32 = 0x282:u32
dsa_R_PF_1_6570:bool = false
dsa_T_t_1_6571:u8 = pad:u8(dsa_mem_ffaf067c_1_5718:u8) - 0xa:u8
dsa_R_CF_1_6572:bool = pad:u8(dsa_mem_ffaf067c_1_5718:u8) < 0xa:u8
dsa_R_OF_1_6573:bool =
  high:bool((pad:u8(dsa_mem_ffaf067c_1_5718:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf067c_1_5718:u8) ^ dsa_T_t_1_6571:u8))
dsa_R_AF_1_6574:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_6571:u8 ^ pad:u8(dsa_mem_ffaf067c_1_5718:u8) ^ 0xa:u8))
dsa_R_PF_3_6577:bool =
  ~low:bool(let dsa_T_acc_1_6575:u8 :=
                                        dsa_T_t_1_6571:u8 >> 4:u8 ^
                                        dsa_T_t_1_6571:u8 in
            let dsa_T_acc_2_6576:u8 :=
                                        dsa_T_acc_1_6575:u8 >> 2:u8 ^
                                        dsa_T_acc_1_6575:u8 in
            dsa_T_acc_2_6576:u8 >> 1:u8 ^ dsa_T_acc_2_6576:u8)
dsa_R_SF_1_6578:bool = high:bool(dsa_T_t_1_6571:u8)
dsa_R_ZF_1_6579:bool = 0:u8 == dsa_T_t_1_6571:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x216, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_6580:bool = false
dsa_R_EIP_1_6581:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_6579:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp156"*/
label nocjmp156
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf067c, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_6582:u32 = 0xffaf0676:u32
dsa_R_DF_1_6583:bool = false
dsa_R_EDX_32_1_6584:u32 = 0xffaf067c:u32
dsa_T_t_1_6585:u32 = dsa_R_EDX_32_1_6584:u32 - dsa_R_EBP_32_1_6582:u32
dsa_R_CF_1_6586:bool = dsa_R_EDX_32_1_6584:u32 < dsa_R_EBP_32_1_6582:u32
dsa_R_OF_1_6587:bool =
  high:bool((dsa_R_EDX_32_1_6584:u32 ^ dsa_R_EBP_32_1_6582:u32) &
            (dsa_R_EDX_32_1_6584:u32 ^ dsa_T_t_1_6585:u32))
dsa_R_AF_1_6588:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6585:u32 ^ dsa_R_EDX_32_1_6584:u32 ^ dsa_R_EBP_32_1_6582:u32))
dsa_R_PF_3_6591:bool =
  ~low:bool(let dsa_T_acc_1_6589:u32 :=
                                         dsa_T_t_1_6585:u32 >> 4:u32 ^
                                         dsa_T_t_1_6585:u32 in
            let dsa_T_acc_2_6590:u32 :=
                                         dsa_T_acc_1_6589:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6589:u32 in
            dsa_T_acc_2_6590:u32 >> 1:u32 ^ dsa_T_acc_2_6590:u32)
dsa_R_SF_1_6592:bool = high:bool(dsa_T_t_1_6585:u32)
dsa_R_ZF_1_6593:bool = 0:u32 == dsa_T_t_1_6585:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf067b, 0, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
  @context "mem32[0xffaf067b]" = 0x39, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_6594:bool = false
dsa_R_AF_1_6595:bool = false
dsa_R_OF_1_6596:bool = false
dsa_R_SF_1_6597:bool = true
dsa_R_DF_1_6598:bool = false
dsa_R_EDX_32_1_6599:u32 = 0xffaf067b:u32
dsa_R_CF_1_6600:bool = false
dsa_R_EFLAGS_1_6601:u32 = 0x286:u32
dsa_R_PF_1_6602:bool = true
dsa_T_t_1_6603:u8 = pad:u8(dsa_mem_ffaf067b_1_5803:u8) - 0xa:u8
dsa_R_CF_1_6604:bool = pad:u8(dsa_mem_ffaf067b_1_5803:u8) < 0xa:u8
dsa_R_OF_1_6605:bool =
  high:bool((pad:u8(dsa_mem_ffaf067b_1_5803:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf067b_1_5803:u8) ^ dsa_T_t_1_6603:u8))
dsa_R_AF_1_6606:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_6603:u8 ^ pad:u8(dsa_mem_ffaf067b_1_5803:u8) ^ 0xa:u8))
dsa_R_PF_3_6609:bool =
  ~low:bool(let dsa_T_acc_1_6607:u8 :=
                                        dsa_T_t_1_6603:u8 >> 4:u8 ^
                                        dsa_T_t_1_6603:u8 in
            let dsa_T_acc_2_6608:u8 :=
                                        dsa_T_acc_1_6607:u8 >> 2:u8 ^
                                        dsa_T_acc_1_6607:u8 in
            dsa_T_acc_2_6608:u8 >> 1:u8 ^ dsa_T_acc_2_6608:u8)
dsa_R_SF_1_6610:bool = high:bool(dsa_T_t_1_6603:u8)
dsa_R_ZF_1_6611:bool = 0:u8 == dsa_T_t_1_6603:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x212, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_6612:bool = false
dsa_R_EIP_1_6613:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_6611:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp157"*/
label nocjmp157
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf067b, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_6614:u32 = 0xffaf0676:u32
dsa_R_DF_1_6615:bool = false
dsa_R_EDX_32_1_6616:u32 = 0xffaf067b:u32
dsa_T_t_1_6617:u32 = dsa_R_EDX_32_1_6616:u32 - dsa_R_EBP_32_1_6614:u32
dsa_R_CF_1_6618:bool = dsa_R_EDX_32_1_6616:u32 < dsa_R_EBP_32_1_6614:u32
dsa_R_OF_1_6619:bool =
  high:bool((dsa_R_EDX_32_1_6616:u32 ^ dsa_R_EBP_32_1_6614:u32) &
            (dsa_R_EDX_32_1_6616:u32 ^ dsa_T_t_1_6617:u32))
dsa_R_AF_1_6620:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6617:u32 ^ dsa_R_EDX_32_1_6616:u32 ^ dsa_R_EBP_32_1_6614:u32))
dsa_R_PF_3_6623:bool =
  ~low:bool(let dsa_T_acc_1_6621:u32 :=
                                         dsa_T_t_1_6617:u32 >> 4:u32 ^
                                         dsa_T_t_1_6617:u32 in
            let dsa_T_acc_2_6622:u32 :=
                                         dsa_T_acc_1_6621:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6621:u32 in
            dsa_T_acc_2_6622:u32 >> 1:u32 ^ dsa_T_acc_2_6622:u32)
dsa_R_SF_1_6624:bool = high:bool(dsa_T_t_1_6617:u32)
dsa_R_ZF_1_6625:bool = 0:u32 == dsa_T_t_1_6617:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf067a, 0, u32, rd
  @context "R_EFLAGS" = 0x282, 0, u32, wr
  @context "mem32[0xffaf067a]" = 0x37, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_6626:bool = false
dsa_R_AF_1_6627:bool = false
dsa_R_OF_1_6628:bool = false
dsa_R_SF_1_6629:bool = true
dsa_R_DF_1_6630:bool = false
dsa_R_EDX_32_1_6631:u32 = 0xffaf067a:u32
dsa_R_CF_1_6632:bool = false
dsa_R_EFLAGS_1_6633:u32 = 0x282:u32
dsa_R_PF_1_6634:bool = false
dsa_T_t_1_6635:u8 = pad:u8(dsa_mem_ffaf067a_1_5888:u8) - 0xa:u8
dsa_R_CF_1_6636:bool = pad:u8(dsa_mem_ffaf067a_1_5888:u8) < 0xa:u8
dsa_R_OF_1_6637:bool =
  high:bool((pad:u8(dsa_mem_ffaf067a_1_5888:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf067a_1_5888:u8) ^ dsa_T_t_1_6635:u8))
dsa_R_AF_1_6638:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_6635:u8 ^ pad:u8(dsa_mem_ffaf067a_1_5888:u8) ^ 0xa:u8))
dsa_R_PF_3_6641:bool =
  ~low:bool(let dsa_T_acc_1_6639:u8 :=
                                        dsa_T_t_1_6635:u8 >> 4:u8 ^
                                        dsa_T_t_1_6635:u8 in
            let dsa_T_acc_2_6640:u8 :=
                                        dsa_T_acc_1_6639:u8 >> 2:u8 ^
                                        dsa_T_acc_1_6639:u8 in
            dsa_T_acc_2_6640:u8 >> 1:u8 ^ dsa_T_acc_2_6640:u8)
dsa_R_SF_1_6642:bool = high:bool(dsa_T_t_1_6635:u8)
dsa_R_ZF_1_6643:bool = 0:u8 == dsa_T_t_1_6635:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x216, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_6644:bool = false
dsa_R_EIP_1_6645:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_6643:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp158"*/
label nocjmp158
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf067a, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_6646:u32 = 0xffaf0676:u32
dsa_R_DF_1_6647:bool = false
dsa_R_EDX_32_1_6648:u32 = 0xffaf067a:u32
dsa_T_t_1_6649:u32 = dsa_R_EDX_32_1_6648:u32 - dsa_R_EBP_32_1_6646:u32
dsa_R_CF_1_6650:bool = dsa_R_EDX_32_1_6648:u32 < dsa_R_EBP_32_1_6646:u32
dsa_R_OF_1_6651:bool =
  high:bool((dsa_R_EDX_32_1_6648:u32 ^ dsa_R_EBP_32_1_6646:u32) &
            (dsa_R_EDX_32_1_6648:u32 ^ dsa_T_t_1_6649:u32))
dsa_R_AF_1_6652:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6649:u32 ^ dsa_R_EDX_32_1_6648:u32 ^ dsa_R_EBP_32_1_6646:u32))
dsa_R_PF_3_6655:bool =
  ~low:bool(let dsa_T_acc_1_6653:u32 :=
                                         dsa_T_t_1_6649:u32 >> 4:u32 ^
                                         dsa_T_t_1_6649:u32 in
            let dsa_T_acc_2_6654:u32 :=
                                         dsa_T_acc_1_6653:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6653:u32 in
            dsa_T_acc_2_6654:u32 >> 1:u32 ^ dsa_T_acc_2_6654:u32)
dsa_R_SF_1_6656:bool = high:bool(dsa_T_t_1_6649:u32)
dsa_R_ZF_1_6657:bool = 0:u32 == dsa_T_t_1_6649:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf0679, 0, u32, rd
  @context "R_EFLAGS" = 0x282, 0, u32, wr
  @context "mem32[0xffaf0679]" = 0x34, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_6658:bool = false
dsa_R_AF_1_6659:bool = false
dsa_R_OF_1_6660:bool = false
dsa_R_SF_1_6661:bool = true
dsa_R_DF_1_6662:bool = false
dsa_R_EDX_32_1_6663:u32 = 0xffaf0679:u32
dsa_R_CF_1_6664:bool = false
dsa_R_EFLAGS_1_6665:u32 = 0x282:u32
dsa_R_PF_1_6666:bool = false
dsa_T_t_1_6667:u8 = pad:u8(dsa_mem_ffaf0679_1_5973:u8) - 0xa:u8
dsa_R_CF_1_6668:bool = pad:u8(dsa_mem_ffaf0679_1_5973:u8) < 0xa:u8
dsa_R_OF_1_6669:bool =
  high:bool((pad:u8(dsa_mem_ffaf0679_1_5973:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf0679_1_5973:u8) ^ dsa_T_t_1_6667:u8))
dsa_R_AF_1_6670:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_6667:u8 ^ pad:u8(dsa_mem_ffaf0679_1_5973:u8) ^ 0xa:u8))
dsa_R_PF_3_6673:bool =
  ~low:bool(let dsa_T_acc_1_6671:u8 :=
                                        dsa_T_t_1_6667:u8 >> 4:u8 ^
                                        dsa_T_t_1_6667:u8 in
            let dsa_T_acc_2_6672:u8 :=
                                        dsa_T_acc_1_6671:u8 >> 2:u8 ^
                                        dsa_T_acc_1_6671:u8 in
            dsa_T_acc_2_6672:u8 >> 1:u8 ^ dsa_T_acc_2_6672:u8)
dsa_R_SF_1_6674:bool = high:bool(dsa_T_t_1_6667:u8)
dsa_R_ZF_1_6675:bool = 0:u8 == dsa_T_t_1_6667:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x212, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_6676:bool = false
dsa_R_EIP_1_6677:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_6675:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp159"*/
label nocjmp159
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf0679, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_6678:u32 = 0xffaf0676:u32
dsa_R_DF_1_6679:bool = false
dsa_R_EDX_32_1_6680:u32 = 0xffaf0679:u32
dsa_T_t_1_6681:u32 = dsa_R_EDX_32_1_6680:u32 - dsa_R_EBP_32_1_6678:u32
dsa_R_CF_1_6682:bool = dsa_R_EDX_32_1_6680:u32 < dsa_R_EBP_32_1_6678:u32
dsa_R_OF_1_6683:bool =
  high:bool((dsa_R_EDX_32_1_6680:u32 ^ dsa_R_EBP_32_1_6678:u32) &
            (dsa_R_EDX_32_1_6680:u32 ^ dsa_T_t_1_6681:u32))
dsa_R_AF_1_6684:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6681:u32 ^ dsa_R_EDX_32_1_6680:u32 ^ dsa_R_EBP_32_1_6678:u32))
dsa_R_PF_3_6687:bool =
  ~low:bool(let dsa_T_acc_1_6685:u32 :=
                                         dsa_T_t_1_6681:u32 >> 4:u32 ^
                                         dsa_T_t_1_6681:u32 in
            let dsa_T_acc_2_6686:u32 :=
                                         dsa_T_acc_1_6685:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6685:u32 in
            dsa_T_acc_2_6686:u32 >> 1:u32 ^ dsa_T_acc_2_6686:u32)
dsa_R_SF_1_6688:bool = high:bool(dsa_T_t_1_6681:u32)
dsa_R_ZF_1_6689:bool = 0:u32 == dsa_T_t_1_6681:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf0678, 0, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
  @context "mem32[0xffaf0678]" = 0x39, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_6690:bool = false
dsa_R_AF_1_6691:bool = false
dsa_R_OF_1_6692:bool = false
dsa_R_SF_1_6693:bool = true
dsa_R_DF_1_6694:bool = false
dsa_R_EDX_32_1_6695:u32 = 0xffaf0678:u32
dsa_R_CF_1_6696:bool = false
dsa_R_EFLAGS_1_6697:u32 = 0x286:u32
dsa_R_PF_1_6698:bool = true
dsa_T_t_1_6699:u8 = pad:u8(dsa_mem_ffaf0678_1_6058:u8) - 0xa:u8
dsa_R_CF_1_6700:bool = pad:u8(dsa_mem_ffaf0678_1_6058:u8) < 0xa:u8
dsa_R_OF_1_6701:bool =
  high:bool((pad:u8(dsa_mem_ffaf0678_1_6058:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf0678_1_6058:u8) ^ dsa_T_t_1_6699:u8))
dsa_R_AF_1_6702:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_6699:u8 ^ pad:u8(dsa_mem_ffaf0678_1_6058:u8) ^ 0xa:u8))
dsa_R_PF_3_6705:bool =
  ~low:bool(let dsa_T_acc_1_6703:u8 :=
                                        dsa_T_t_1_6699:u8 >> 4:u8 ^
                                        dsa_T_t_1_6699:u8 in
            let dsa_T_acc_2_6704:u8 :=
                                        dsa_T_acc_1_6703:u8 >> 2:u8 ^
                                        dsa_T_acc_1_6703:u8 in
            dsa_T_acc_2_6704:u8 >> 1:u8 ^ dsa_T_acc_2_6704:u8)
dsa_R_SF_1_6706:bool = high:bool(dsa_T_t_1_6699:u8)
dsa_R_ZF_1_6707:bool = 0:u8 == dsa_T_t_1_6699:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x212, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_6708:bool = false
dsa_R_EIP_1_6709:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_6707:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp160"*/
label nocjmp160
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf0678, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_6710:u32 = 0xffaf0676:u32
dsa_R_DF_1_6711:bool = false
dsa_R_EDX_32_1_6712:u32 = 0xffaf0678:u32
dsa_T_t_1_6713:u32 = dsa_R_EDX_32_1_6712:u32 - dsa_R_EBP_32_1_6710:u32
dsa_R_CF_1_6714:bool = dsa_R_EDX_32_1_6712:u32 < dsa_R_EBP_32_1_6710:u32
dsa_R_OF_1_6715:bool =
  high:bool((dsa_R_EDX_32_1_6712:u32 ^ dsa_R_EBP_32_1_6710:u32) &
            (dsa_R_EDX_32_1_6712:u32 ^ dsa_T_t_1_6713:u32))
dsa_R_AF_1_6716:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6713:u32 ^ dsa_R_EDX_32_1_6712:u32 ^ dsa_R_EBP_32_1_6710:u32))
dsa_R_PF_3_6719:bool =
  ~low:bool(let dsa_T_acc_1_6717:u32 :=
                                         dsa_T_t_1_6713:u32 >> 4:u32 ^
                                         dsa_T_t_1_6713:u32 in
            let dsa_T_acc_2_6718:u32 :=
                                         dsa_T_acc_1_6717:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6717:u32 in
            dsa_T_acc_2_6718:u32 >> 1:u32 ^ dsa_T_acc_2_6718:u32)
dsa_R_SF_1_6720:bool = high:bool(dsa_T_t_1_6713:u32)
dsa_R_ZF_1_6721:bool = 0:u32 == dsa_T_t_1_6713:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf0677, 0, u32, rd
  @context "R_EFLAGS" = 0x286, 0, u32, wr
  @context "mem32[0xffaf0677]" = 0x30, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_6722:bool = false
dsa_R_AF_1_6723:bool = false
dsa_R_OF_1_6724:bool = false
dsa_R_SF_1_6725:bool = true
dsa_R_DF_1_6726:bool = false
dsa_R_EDX_32_1_6727:u32 = 0xffaf0677:u32
dsa_R_CF_1_6728:bool = false
dsa_R_EFLAGS_1_6729:u32 = 0x286:u32
dsa_R_PF_1_6730:bool = true
dsa_T_t_1_6731:u8 = pad:u8(dsa_mem_ffaf0677_1_6143:u8) - 0xa:u8
dsa_R_CF_1_6732:bool = pad:u8(dsa_mem_ffaf0677_1_6143:u8) < 0xa:u8
dsa_R_OF_1_6733:bool =
  high:bool((pad:u8(dsa_mem_ffaf0677_1_6143:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf0677_1_6143:u8) ^ dsa_T_t_1_6731:u8))
dsa_R_AF_1_6734:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_6731:u8 ^ pad:u8(dsa_mem_ffaf0677_1_6143:u8) ^ 0xa:u8))
dsa_R_PF_3_6737:bool =
  ~low:bool(let dsa_T_acc_1_6735:u8 :=
                                        dsa_T_t_1_6731:u8 >> 4:u8 ^
                                        dsa_T_t_1_6731:u8 in
            let dsa_T_acc_2_6736:u8 :=
                                        dsa_T_acc_1_6735:u8 >> 2:u8 ^
                                        dsa_T_acc_1_6735:u8 in
            dsa_T_acc_2_6736:u8 >> 1:u8 ^ dsa_T_acc_2_6736:u8)
dsa_R_SF_1_6738:bool = high:bool(dsa_T_t_1_6731:u8)
dsa_R_ZF_1_6739:bool = 0:u8 == dsa_T_t_1_6731:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x212, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_6740:bool = false
dsa_R_EIP_1_6741:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_6739:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp161"*/
label nocjmp161
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf0677, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x212, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_6742:u32 = 0xffaf0676:u32
dsa_R_DF_1_6743:bool = false
dsa_R_EDX_32_1_6744:u32 = 0xffaf0677:u32
dsa_T_t_1_6745:u32 = dsa_R_EDX_32_1_6744:u32 - dsa_R_EBP_32_1_6742:u32
dsa_R_CF_1_6746:bool = dsa_R_EDX_32_1_6744:u32 < dsa_R_EBP_32_1_6742:u32
dsa_R_OF_1_6747:bool =
  high:bool((dsa_R_EDX_32_1_6744:u32 ^ dsa_R_EBP_32_1_6742:u32) &
            (dsa_R_EDX_32_1_6744:u32 ^ dsa_T_t_1_6745:u32))
dsa_R_AF_1_6748:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6745:u32 ^ dsa_R_EDX_32_1_6744:u32 ^ dsa_R_EBP_32_1_6742:u32))
dsa_R_PF_3_6751:bool =
  ~low:bool(let dsa_T_acc_1_6749:u32 :=
                                         dsa_T_t_1_6745:u32 >> 4:u32 ^
                                         dsa_T_t_1_6745:u32 in
            let dsa_T_acc_2_6750:u32 :=
                                         dsa_T_acc_1_6749:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6749:u32 in
            dsa_T_acc_2_6750:u32 >> 1:u32 ^ dsa_T_acc_2_6750:u32)
dsa_R_SF_1_6752:bool = high:bool(dsa_T_t_1_6745:u32)
dsa_R_ZF_1_6753:bool = 0:u32 == dsa_T_t_1_6745:u32
addr 0xdcf2f38b @asm "cmp    BYTE PTR [edx],0xa" @tid "0"
  @context "R_EDX_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x282, 0, u32, wr
  @context "mem32[0xffaf0676]" = 0x31, -1, u8, rd
label pc_0xdcf2f38b
dsa_R_ZF_1_6754:bool = false
dsa_R_AF_1_6755:bool = false
dsa_R_OF_1_6756:bool = false
dsa_R_SF_1_6757:bool = true
dsa_R_DF_1_6758:bool = false
dsa_R_EDX_32_1_6759:u32 = 0xffaf0676:u32
dsa_R_CF_1_6760:bool = false
dsa_R_EFLAGS_1_6761:u32 = 0x282:u32
dsa_R_PF_1_6762:bool = false
dsa_T_t_1_6763:u8 = pad:u8(dsa_mem_ffaf0676_1_6228:u8) - 0xa:u8
dsa_R_CF_1_6764:bool = pad:u8(dsa_mem_ffaf0676_1_6228:u8) < 0xa:u8
dsa_R_OF_1_6765:bool =
  high:bool((pad:u8(dsa_mem_ffaf0676_1_6228:u8) ^ 0xa:u8) &
            (pad:u8(dsa_mem_ffaf0676_1_6228:u8) ^ dsa_T_t_1_6763:u8))
dsa_R_AF_1_6766:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_6763:u8 ^ pad:u8(dsa_mem_ffaf0676_1_6228:u8) ^ 0xa:u8))
dsa_R_PF_3_6769:bool =
  ~low:bool(let dsa_T_acc_1_6767:u8 :=
                                        dsa_T_t_1_6763:u8 >> 4:u8 ^
                                        dsa_T_t_1_6763:u8 in
            let dsa_T_acc_2_6768:u8 :=
                                        dsa_T_acc_1_6767:u8 >> 2:u8 ^
                                        dsa_T_acc_1_6767:u8 in
            dsa_T_acc_2_6768:u8 >> 1:u8 ^ dsa_T_acc_2_6768:u8)
dsa_R_SF_1_6770:bool = high:bool(dsa_T_t_1_6763:u8)
dsa_R_ZF_1_6771:bool = 0:u8 == dsa_T_t_1_6763:u8
addr 0xdcf2f38e @asm "je     0x00000000dcf2f3b8" @tid "0"
  @context "R_EIP" = 0xdcf2f38e, 0, u32, rw
  @context "R_EFLAGS" = 0x216, -1, u32, rd
label pc_0xdcf2f38e
dsa_R_DF_1_6772:bool = false
dsa_R_EIP_1_6773:u32 = 0xdcf2f38e:u32
assert ~dsa_R_ZF_1_6771:bool
/*Removed: cjmp R_ZF_662:bool, 0xdcf2f3b8:u32, "nocjmp162"*/
label nocjmp162
addr 0xdcf2f390 @asm "cmp    edx,ebp" @tid "0"
  @context "R_EDX_32" = 0xffaf0676, 0, u32, rd
  @context "R_EBP_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x216, -1, u32, wr
label pc_0xdcf2f390
dsa_R_EBP_32_1_6774:u32 = 0xffaf0676:u32
dsa_R_DF_1_6775:bool = false
dsa_R_EDX_32_1_6776:u32 = 0xffaf0676:u32
dsa_T_t_1_6777:u32 = dsa_R_EDX_32_1_6776:u32 - dsa_R_EBP_32_1_6774:u32
dsa_R_CF_1_6778:bool = dsa_R_EDX_32_1_6776:u32 < dsa_R_EBP_32_1_6774:u32
dsa_R_OF_1_6779:bool =
  high:bool((dsa_R_EDX_32_1_6776:u32 ^ dsa_R_EBP_32_1_6774:u32) &
            (dsa_R_EDX_32_1_6776:u32 ^ dsa_T_t_1_6777:u32))
dsa_R_AF_1_6780:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6777:u32 ^ dsa_R_EDX_32_1_6776:u32 ^ dsa_R_EBP_32_1_6774:u32))
dsa_R_PF_3_6783:bool =
  ~low:bool(let dsa_T_acc_1_6781:u32 :=
                                         dsa_T_t_1_6777:u32 >> 4:u32 ^
                                         dsa_T_t_1_6777:u32 in
            let dsa_T_acc_2_6782:u32 :=
                                         dsa_T_acc_1_6781:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6781:u32 in
            dsa_T_acc_2_6782:u32 >> 1:u32 ^ dsa_T_acc_2_6782:u32)
dsa_R_SF_1_6784:bool = high:bool(dsa_T_t_1_6777:u32)
dsa_R_ZF_1_6785:bool = 0:u32 == dsa_T_t_1_6777:u32
addr 0xdcf3cc3a @asm "movs   WORD PTR es:[edi],WORD PTR ds:[esi]" @tid "0"
  @context "R_EDI_32" = 0xdcb9d025, 0, u32, rd
  @context "R_ESI_32" = 0xffaf0676, 0, u32, rd
  @context "R_EFLAGS" = 0x203, 0, u32, rd
  @context "mem32[0xffaf0676]" = 0x31, -1, u8, rd
  @context "mem32[0xffaf0677]" = 0x30, -1, u8, rd
  @context "mem32[0xdcb9d025]" = 0x0, 0, u8, wr
  @context "mem32[0xdcb9d026]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3a
dsa_mem_dcb9d026_1_6786:u8 = low:u8(0:u8)
dsa_mem_dcb9d025_1_6787:u8 = low:u8(0:u8)
dsa_R_ZF_1_6788:bool = false
dsa_R_ESI_32_1_6789:u32 = 0xffaf0676:u32
dsa_R_AF_1_6790:bool = false
dsa_R_OF_1_6791:bool = false
dsa_R_SF_1_6792:bool = false
dsa_R_DF_1_6793:bool = false
dsa_R_EDI_32_1_6794:u32 = 0xdcb9d025:u32
dsa_R_CF_1_6795:bool = true
dsa_R_EFLAGS_1_6796:u32 = 0x203:u32
dsa_R_PF_1_6797:bool = false
dsa_mem_dcb9d025_1_6798:u8 =
  low:u8(pad:u16(dsa_mem_ffaf0677_1_6143:u8) << 8:u16 |
         pad:u16(dsa_mem_ffaf0676_1_6228:u8))
dsa_mem_dcb9d026_1_6799:u8 =
  low:u8((pad:u16(dsa_mem_ffaf0677_1_6143:u8) << 8:u16 |
         pad:u16(dsa_mem_ffaf0676_1_6228:u8)) >> 8:u16)
dsa_R_ESI_32_1_6800:u32 =
  dsa_R_ESI_32_1_6789:u32 +
  (if dsa_R_DF_1_6793:bool == false then 1:u32 else -1:u32) * 2:u32
dsa_R_EDI_32_1_6801:u32 =
  dsa_R_EDI_32_1_6794:u32 +
  (if dsa_R_DF_1_6793:bool == false then 1:u32 else -1:u32) * 2:u32
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xdcb9d027, 0, u32, rd
  @context "R_ESI_32" = 0xffaf0678, 0, u32, rd
  @context "R_ECX_32" = 0x2, 0, u32, rw
  @context "R_EFLAGS" = 0x203, 0, u32, rd
  @context "mem32[0xffaf0678]" = 0x39, -1, u8, rd
  @context "mem32[0xffaf0679]" = 0x34, -1, u8, rd
  @context "mem32[0xffaf067a]" = 0x37, -1, u8, rd
  @context "mem32[0xffaf067b]" = 0x39, -1, u8, rd
  @context "mem32[0xdcb9d027]" = 0x0, 0, u8, wr
  @context "mem32[0xdcb9d028]" = 0x0, 0, u8, wr
  @context "mem32[0xdcb9d029]" = 0x0, 0, u8, wr
  @context "mem32[0xdcb9d02a]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_dcb9d029_1_6802:u8 = low:u8(0:u8)
dsa_mem_dcb9d028_1_6803:u8 = low:u8(0:u8)
dsa_mem_dcb9d02a_1_6804:u8 = low:u8(0:u8)
dsa_mem_dcb9d027_1_6805:u8 = low:u8(0:u8)
dsa_R_ZF_1_6806:bool = false
dsa_R_ESI_32_1_6807:u32 = 0xffaf0678:u32
dsa_R_AF_1_6808:bool = false
dsa_R_OF_1_6809:bool = false
dsa_R_ECX_32_1_6810:u32 = 2:u32
dsa_R_SF_1_6811:bool = false
dsa_R_DF_1_6812:bool = false
dsa_R_EDI_32_1_6813:u32 = 0xdcb9d027:u32
dsa_R_CF_1_6814:bool = true
dsa_R_EFLAGS_1_6815:u32 = 0x203:u32
dsa_R_PF_1_6816:bool = false
assert ~(dsa_R_ECX_32_1_6810:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp164"*/
label nocjmp164
dsa_mem_dcb9d027_1_6817:u8 =
  low:u8(pad:u32(dsa_mem_ffaf067b_1_5803:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067a_1_5888:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf0679_1_5973:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf0678_1_6058:u8))))
dsa_mem_dcb9d028_1_6818:u8 =
  low:u8((pad:u32(dsa_mem_ffaf067b_1_5803:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067a_1_5888:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf0679_1_5973:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf0678_1_6058:u8)))) >> 8:u32)
dsa_mem_dcb9d029_1_6819:u8 =
  low:u8((pad:u32(dsa_mem_ffaf067b_1_5803:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067a_1_5888:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf0679_1_5973:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf0678_1_6058:u8)))) >> 0x10:u32)
dsa_mem_dcb9d02a_1_6820:u8 =
  low:u8((pad:u32(dsa_mem_ffaf067b_1_5803:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067a_1_5888:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf0679_1_5973:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf0678_1_6058:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_6821:u32 =
  dsa_R_ESI_32_1_6807:u32 +
  (if dsa_R_DF_1_6812:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_6822:u32 =
  dsa_R_EDI_32_1_6813:u32 +
  (if dsa_R_DF_1_6812:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_6823:u32 = dsa_R_ECX_32_1_6810:u32 - 1:u32
assert ~(dsa_R_ECX_32_1_6823:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp163"*/
label nocjmp163
/*Removed: jmp 0xdcf3cc3c:u32*/
addr 0xdcf3cc3c @asm "rep movs DWORD PTR es:[edi],DWORD PTR ds:[esi]"
  @tid "0" @context "R_EDI_32" = 0xdcb9d02b, 0, u32, rd
  @context "R_ESI_32" = 0xffaf067c, 0, u32, rd
  @context "R_ECX_32" = 0x1, -1, u32, rw
  @context "R_EFLAGS" = 0x203, 0, u32, rd
  @context "mem32[0xffaf067c]" = 0x35, -1, u8, rd
  @context "mem32[0xffaf067d]" = 0x35, -1, u8, rd
  @context "mem32[0xffaf067e]" = 0x38, -1, u8, rd
  @context "mem32[0xffaf067f]" = 0x35, -1, u8, rd
  @context "mem32[0xdcb9d02b]" = 0x0, 0, u8, wr
  @context "mem32[0xdcb9d02c]" = 0x0, 0, u8, wr
  @context "mem32[0xdcb9d02d]" = 0x0, 0, u8, wr
  @context "mem32[0xdcb9d02e]" = 0x0, 0, u8, wr
label pc_0xdcf3cc3c
dsa_mem_dcb9d02c_1_6824:u8 = low:u8(0:u8)
dsa_mem_dcb9d02b_1_6825:u8 = low:u8(0:u8)
dsa_mem_dcb9d02d_1_6826:u8 = low:u8(0:u8)
dsa_mem_dcb9d02e_1_6827:u8 = low:u8(0:u8)
dsa_R_ZF_1_6828:bool = false
dsa_R_ESI_32_1_6829:u32 = 0xffaf067c:u32
dsa_R_AF_1_6830:bool = false
dsa_R_OF_1_6831:bool = false
dsa_R_SF_1_6832:bool = false
dsa_R_DF_1_6833:bool = false
dsa_R_EDI_32_1_6834:u32 = 0xdcb9d02b:u32
dsa_R_CF_1_6835:bool = true
dsa_R_EFLAGS_1_6836:u32 = 0x203:u32
dsa_R_PF_1_6837:bool = false
assert ~(dsa_R_ECX_32_1_6823:u32 == 0:u32)
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp166"*/
label nocjmp166
dsa_mem_dcb9d02b_1_6838:u8 =
  low:u8(pad:u32(dsa_mem_ffaf067f_1_5463:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067e_1_5548:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf067d_1_5633:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf067c_1_5718:u8))))
dsa_mem_dcb9d02c_1_6839:u8 =
  low:u8((pad:u32(dsa_mem_ffaf067f_1_5463:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067e_1_5548:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf067d_1_5633:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf067c_1_5718:u8)))) >> 8:u32)
dsa_mem_dcb9d02d_1_6840:u8 =
  low:u8((pad:u32(dsa_mem_ffaf067f_1_5463:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067e_1_5548:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf067d_1_5633:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf067c_1_5718:u8)))) >> 0x10:u32)
dsa_mem_dcb9d02e_1_6841:u8 =
  low:u8((pad:u32(dsa_mem_ffaf067f_1_5463:u8) << 0x18:u32 |
         (pad:u32(dsa_mem_ffaf067e_1_5548:u8) << 0x10:u32 |
         (pad:u32(dsa_mem_ffaf067d_1_5633:u8) << 8:u32 |
         pad:u32(dsa_mem_ffaf067c_1_5718:u8)))) >> 0x18:u32)
dsa_R_ESI_32_1_6842:u32 =
  dsa_R_ESI_32_1_6829:u32 +
  (if dsa_R_DF_1_6833:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_EDI_32_1_6843:u32 =
  dsa_R_EDI_32_1_6834:u32 +
  (if dsa_R_DF_1_6833:bool == false then 1:u32 else -1:u32) * 4:u32
dsa_R_ECX_32_1_6844:u32 = dsa_R_ECX_32_1_6823:u32 - 1:u32
assert dsa_R_ECX_32_1_6844:u32 == 0:u32
/*Removed: cjmp R_ECX_32_667:u32 == 0:u32, 0xdcf3cc3e:u32, "nocjmp165"*/
addr 0xdcf3ef8b @asm "mov    ecx,edx" @tid "0"
  @context "R_ECX_32" = 0x0, -1, u32, wr
  @context "R_EDX_32" = 0x2525, 0, u32, rd
label pc_0xdcf3ef8b
dsa_R_EDX_32_1_6845:u32 = 0x2525:u32
dsa_R_ECX_32_1_6846:u32 = dsa_R_EDX_32_1_6845:u32
addr 0xf76f825b @asm "mov    DWORD PTR [ebp-0x2c],eax" @tid "0"
  @context "R_EBP_32" = 0xffaf06a0, 0, u32, rd
  @context "R_EAX_32" = 0x8048208, 0, u32, rd
  @context "mem32[0xffaf0674]" = 0x38, 0, u8, wr
  @context "mem32[0xffaf0675]" = 0x82, 0, u8, wr
  @context "mem32[0xffaf0676]" = 0x31, -1, u8, wr
  @context "mem32[0xffaf0677]" = 0x30, -1, u8, wr
label pc_0xf76f825b
dsa_mem_ffaf0674_1_6847:u8 = low:u8(0x38:u8)
dsa_mem_ffaf0675_1_6848:u8 = low:u8(0x82:u8)
dsa_R_EBP_32_1_6849:u32 = 0xffaf06a0:u32
dsa_R_EAX_32_1_6850:u32 = 0x8048208:u32
dsa_mem_ffaf0674_1_6851:u8 = low:u8(dsa_R_EAX_32_1_6850:u32)
dsa_mem_ffaf0675_1_6852:u8 = low:u8(dsa_R_EAX_32_1_6850:u32 >> 8:u32)
dsa_mem_ffaf0676_1_6853:u8 = low:u8(dsa_R_EAX_32_1_6850:u32 >> 0x10:u32)
dsa_mem_ffaf0677_1_6854:u8 = low:u8(dsa_R_EAX_32_1_6850:u32 >> 0x18:u32)
addr 0xdcf2dd59 @asm "call   0x00000000dcfe8cbb" @tid "0"
  @context "R_EIP" = 0xdcf2dd59, 0, u32, rw
  @context "R_ESP_32" = 0xffaf0680, 0, u32, rd
  @context "mem32[0xffaf067c]" = 0x35, -1, u8, wr
  @context "mem32[0xffaf067d]" = 0x35, -1, u8, wr
  @context "mem32[0xffaf067e]" = 0x38, -1, u8, wr
  @context "mem32[0xffaf067f]" = 0x35, -1, u8, wr
label pc_0xdcf2dd59
dsa_R_ESP_32_1_6855:u32 = 0xffaf0680:u32
dsa_R_EIP_1_6856:u32 = 0xdcf2dd59:u32
dsa_R_ESP_32_1_6857:u32 = dsa_R_ESP_32_1_6855:u32 - 4:u32
dsa_mem_ffaf067c_1_6858:u8 = low:u8(0xdcf2dd5e:u32)
dsa_mem_ffaf067d_1_6859:u8 = low:u8(0xdcf2dd5e:u32 >> 8:u32)
dsa_mem_ffaf067e_1_6860:u8 = low:u8(0xdcf2dd5e:u32 >> 0x10:u32)
dsa_mem_ffaf067f_1_6861:u8 = low:u8(0xdcf2dd5e:u32 >> 0x18:u32)
/*Removed: jmp 0xdcfe8cbb:u32 @str "call"*/
addr 0xdcf34a62 @asm "mov    DWORD PTR [esp+0x68],edi" @tid "0"
  @context "R_ESP_32" = 0xffaf0610, 0, u32, rd
  @context "R_EDI_32" = 0x0, 0, u32, rd
  @context "mem32[0xffaf0678]" = 0x39, -1, u8, wr
  @context "mem32[0xffaf0679]" = 0x34, -1, u8, wr
  @context "mem32[0xffaf067a]" = 0x37, -1, u8, wr
  @context "mem32[0xffaf067b]" = 0x39, -1, u8, wr
label pc_0xdcf34a62
dsa_R_EDI_32_1_6862:u32 = 0:u32
dsa_R_ESP_32_1_6863:u32 = 0xffaf0610:u32
dsa_mem_ffaf0678_1_6864:u8 = low:u8(dsa_R_EDI_32_1_6862:u32)
dsa_mem_ffaf0679_1_6865:u8 = low:u8(dsa_R_EDI_32_1_6862:u32 >> 8:u32)
dsa_mem_ffaf067a_1_6866:u8 = low:u8(dsa_R_EDI_32_1_6862:u32 >> 0x10:u32)
dsa_mem_ffaf067b_1_6867:u8 = low:u8(dsa_R_EDI_32_1_6862:u32 >> 0x18:u32)
addr 0x80488dc @asm "mov    eax,DWORD PTR [eax+0x4]" @tid "0"
  @context "R_EAX_32" = 0xffaf071c, 0, u32, wr
  @context "R_EAX_32" = 0xffaf071c, 0, u32, rd
  @context "mem32[0xffaf0720]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0721]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0722]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0723]" = 0x41, -1, u8, rd
label pc_0x80488dc
dsa_R_EAX_32_1_6868:u32 = 0xffaf071c:u32
dsa_R_EAX_32_1_6869:u32 =
  pad:u32(dsa_mem_ffaf0723_1_2445:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf0722_1_2444:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf0721_1_2426:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf0720_1_2425:u8)))
addr 0x80488df @asm "mov    DWORD PTR [esp+0x8],eax" @tid "0"
  @context "R_ESP_32" = 0xffaf06c0, 0, u32, rd
  @context "R_EAX_32" = 0x41414141, -1, u32, rd
  @context "mem32[0xffaf06c8]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf06c9]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf06ca]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf06cb]" = 0x41, -1, u8, wr
label pc_0x80488df
dsa_R_ESP_32_1_6870:u32 = 0xffaf06c0:u32
dsa_mem_ffaf06c8_1_6871:u8 = low:u8(dsa_R_EAX_32_1_6869:u32)
dsa_mem_ffaf06c9_1_6872:u8 = low:u8(dsa_R_EAX_32_1_6869:u32 >> 8:u32)
dsa_mem_ffaf06ca_1_6873:u8 = low:u8(dsa_R_EAX_32_1_6869:u32 >> 0x10:u32)
dsa_mem_ffaf06cb_1_6874:u8 = low:u8(dsa_R_EAX_32_1_6869:u32 >> 0x18:u32)
addr 0x80488e3 @asm "mov    eax,DWORD PTR [ebp+0x8]" @tid "0"
  @context "R_EAX_32" = 0x41414141, -1, u32, wr
  @context "R_EBP_32" = 0xffaf06f8, 0, u32, rd
  @context "mem32[0xffaf0700]" = 0x1c, 0, u8, rd
  @context "mem32[0xffaf0701]" = 0x7, 0, u8, rd
  @context "mem32[0xffaf0702]" = 0xaf, 0, u8, rd
  @context "mem32[0xffaf0703]" = 0xff, 0, u8, rd
label pc_0x80488e3
dsa_mem_ffaf0702_1_6875:u8 = low:u8(0xaf:u8)
dsa_mem_ffaf0703_1_6876:u8 = low:u8(-1:u8)
dsa_mem_ffaf0700_1_6877:u8 = low:u8(0x1c:u8)
dsa_mem_ffaf0701_1_6878:u8 = low:u8(7:u8)
dsa_R_EBP_32_1_6879:u32 = 0xffaf06f8:u32
dsa_R_EAX_32_1_6880:u32 =
  pad:u32(dsa_mem_ffaf0703_1_6876:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf0702_1_6875:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf0701_1_6878:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf0700_1_6877:u8)))
addr 0x80488e6 @asm "mov    DWORD PTR [esp+0x4],eax" @tid "0"
  @context "R_ESP_32" = 0xffaf06c0, 0, u32, rd
  @context "R_EAX_32" = 0xffaf071c, 0, u32, rd
  @context "mem32[0xffaf06c4]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf06c5]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf06c6]" = 0x41, -1, u8, wr
  @context "mem32[0xffaf06c7]" = 0x41, -1, u8, wr
label pc_0x80488e6
dsa_R_EAX_32_1_6881:u32 = 0xffaf071c:u32
dsa_R_ESP_32_1_6882:u32 = 0xffaf06c0:u32
dsa_mem_ffaf06c4_1_6883:u8 = low:u8(dsa_R_EAX_32_1_6881:u32)
dsa_mem_ffaf06c5_1_6884:u8 = low:u8(dsa_R_EAX_32_1_6881:u32 >> 8:u32)
dsa_mem_ffaf06c6_1_6885:u8 = low:u8(dsa_R_EAX_32_1_6881:u32 >> 0x10:u32)
dsa_mem_ffaf06c7_1_6886:u8 = low:u8(dsa_R_EAX_32_1_6881:u32 >> 0x18:u32)
addr 0xdcff5a51 @asm "mov    ecx,DWORD PTR [esp+0x10]" @tid "0"
  @context "R_ECX_32" = 0xdd06d420, 0, u32, wr
  @context "R_ESP_32" = 0xffaf06b8, 0, u32, rd
  @context "mem32[0xffaf06c8]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf06c9]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf06ca]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf06cb]" = 0x41, -1, u8, rd
label pc_0xdcff5a51
dsa_R_ECX_32_1_6887:u32 = 0xdd06d420:u32
dsa_R_ESP_32_1_6888:u32 = 0xffaf06b8:u32
dsa_R_ECX_32_1_6889:u32 =
  pad:u32(dsa_mem_ffaf06cb_1_6874:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_ffaf06ca_1_6873:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_ffaf06c9_1_6872:u8) << 8:u32 |
  pad:u32(dsa_mem_ffaf06c8_1_6871:u8)))
addr 0xdcff5a5d @asm "cmp    ecx,0x30" @tid "0"
  @context "R_ECX_32" = 0x41414141, -1, u32, rd
  @context "R_EFLAGS" = 0x246, 0, u32, wr
label pc_0xdcff5a5d
dsa_R_ZF_1_6890:bool = true
dsa_R_AF_1_6891:bool = false
dsa_R_OF_1_6892:bool = false
dsa_R_SF_1_6893:bool = false
dsa_R_DF_1_6894:bool = false
dsa_R_CF_1_6895:bool = false
dsa_R_EFLAGS_1_6896:u32 = 0x246:u32
dsa_R_PF_1_6897:bool = true
dsa_T_t_1_6898:u32 = dsa_R_ECX_32_1_6889:u32 - 0x30:u32
dsa_R_CF_1_6899:bool = dsa_R_ECX_32_1_6889:u32 < 0x30:u32
dsa_R_OF_1_6900:bool =
  high:bool((dsa_R_ECX_32_1_6889:u32 ^ 0x30:u32) &
            (dsa_R_ECX_32_1_6889:u32 ^ dsa_T_t_1_6898:u32))
dsa_R_AF_1_6901:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_T_t_1_6898:u32 ^ dsa_R_ECX_32_1_6889:u32 ^ 0x30:u32))
dsa_R_PF_3_6904:bool =
  ~low:bool(let dsa_T_acc_1_6902:u32 :=
                                         dsa_T_t_1_6898:u32 >> 4:u32 ^
                                         dsa_T_t_1_6898:u32 in
            let dsa_T_acc_2_6903:u32 :=
                                         dsa_T_acc_1_6902:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6902:u32 in
            dsa_T_acc_2_6903:u32 >> 1:u32 ^ dsa_T_acc_2_6903:u32)
dsa_R_SF_1_6905:bool = high:bool(dsa_T_t_1_6898:u32)
dsa_R_ZF_1_6906:bool = 0:u32 == dsa_T_t_1_6898:u32
addr 0xdcff5a60 @asm "jae    0x00000000dcff5a90" @tid "0"
  @context "R_EIP" = 0xdcff5a60, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff5a60
dsa_R_DF_1_6907:bool = false
dsa_R_EIP_1_6908:u32 = 0xdcff5a60:u32
assert ~dsa_R_CF_1_6899:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff5a90:u32, "nocjmp167"*/
addr 0xdcff5a90 @asm "movdqu xmm0,XMMWORD PTR [eax]" @tid "0"
  @context "R_YMM0" = 0x0, 0, u256, wr
  @context "R_EAX_32" = 0xffaf071c, 0, u32, rd
  @context "mem32[0xffaf071c]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf071d]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf071e]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf071f]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0720]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0721]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0722]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0723]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0724]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0725]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0726]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0727]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0728]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0729]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf072a]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf072b]" = 0x41, -1, u8, rd
label pc_0xdcff5a90
dsa_R_EAX_32_1_6909:u32 = 0xffaf071c:u32
dsa_R_YMM0_1_6910:u256 = 0:u256
dsa_R_YMM0_1_6911:u256 =
  concat:[extract:255:128:[dsa_R_YMM0_1_6910:u256]][
   pad:u128(dsa_mem_ffaf072b_1_2487:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf072a_1_2486:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0729_1_2468:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0728_1_2467:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf0727_1_2466:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf0726_1_2465:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf0725_1_2447:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf0724_1_2446:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf0723_1_2445:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf0722_1_2444:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0721_1_2426:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0720_1_2425:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf071f_1_2424:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf071e_1_2423:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf071d_1_2405:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf071c_1_2404:u8)))))))))))))))]
addr 0xdcff5a97 @asm "and    edx,0xfffffff0" @tid "0"
  @context "R_EDX_32" = 0x8656008, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff5a97
dsa_R_DF_1_6912:bool = false
dsa_R_EDX_32_1_6913:u32 = 0x8656008:u32
dsa_R_EDX_32_1_6914:u32 = dsa_R_EDX_32_1_6913:u32 & 0xfffffff0:u32
dsa_R_OF_1_6915:bool = false
dsa_R_CF_1_6916:bool = false
dsa_R_AF_1_6917:bool = unknown "AF is undefined after and":bool
dsa_R_PF_3_6920:bool =
  ~low:bool(let dsa_T_acc_1_6918:u32 :=
                                         dsa_R_EDX_32_1_6914:u32 >> 4:u32 ^
                                         dsa_R_EDX_32_1_6914:u32 in
            let dsa_T_acc_2_6919:u32 :=
                                         dsa_T_acc_1_6918:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6918:u32 in
            dsa_T_acc_2_6919:u32 >> 1:u32 ^ dsa_T_acc_2_6919:u32)
dsa_R_SF_1_6921:bool = high:bool(dsa_R_EDX_32_1_6914:u32)
dsa_R_ZF_1_6922:bool = 0:u32 == dsa_R_EDX_32_1_6914:u32
addr 0xdcff5aa2 @asm "add    ecx,edi" @tid "0"
  @context "R_ECX_32" = 0x41414141, -1, u32, rw
  @context "R_EDI_32" = 0xfffffff8, 0, u32, rd
  @context "R_EFLAGS" = 0x283, 0, u32, wr
label pc_0xdcff5aa2
dsa_R_ZF_1_6923:bool = false
dsa_R_AF_1_6924:bool = false
dsa_R_OF_1_6925:bool = false
dsa_R_SF_1_6926:bool = true
dsa_R_DF_1_6927:bool = false
dsa_R_EDI_32_1_6928:u32 = -8:u32
dsa_R_CF_1_6929:bool = true
dsa_R_EFLAGS_1_6930:u32 = 0x283:u32
dsa_R_PF_1_6931:bool = false
dsa_T_t1_1_6932:u32 = dsa_R_ECX_32_1_6889:u32
dsa_T_t2_1_6933:u32 = dsa_R_EDI_32_1_6928:u32
dsa_R_ECX_32_1_6934:u32 = dsa_R_ECX_32_1_6889:u32 + dsa_T_t2_1_6933:u32
dsa_R_CF_1_6935:bool = dsa_R_ECX_32_1_6934:u32 < dsa_T_t1_1_6932:u32
dsa_R_OF_1_6936:bool =
  high:bool((dsa_T_t1_1_6932:u32 ^ ~dsa_T_t2_1_6933:u32) &
            (dsa_T_t1_1_6932:u32 ^ dsa_R_ECX_32_1_6934:u32))
dsa_R_AF_1_6937:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_ECX_32_1_6934:u32 ^ dsa_T_t1_1_6932:u32 ^ dsa_T_t2_1_6933:u32))
dsa_R_PF_3_6940:bool =
  ~low:bool(let dsa_T_acc_1_6938:u32 :=
                                         dsa_R_ECX_32_1_6934:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_6934:u32 in
            let dsa_T_acc_2_6939:u32 :=
                                         dsa_T_acc_1_6938:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6938:u32 in
            dsa_T_acc_2_6939:u32 >> 1:u32 ^ dsa_T_acc_2_6939:u32)
dsa_R_SF_1_6941:bool = high:bool(dsa_R_ECX_32_1_6934:u32)
dsa_R_ZF_1_6942:bool = 0:u32 == dsa_R_ECX_32_1_6934:u32
addr 0xdcff5aa4 @asm "sub    eax,edi" @tid "0"
  @context "R_EAX_32" = 0xffaf071c, 0, u32, rw
  @context "R_EDI_32" = 0xfffffff8, 0, u32, rd
  @context "R_EFLAGS" = 0x207, -1, u32, wr
label pc_0xdcff5aa4
dsa_R_DF_1_6943:bool = false
dsa_R_EAX_32_1_6944:u32 = 0xffaf071c:u32
dsa_R_EDI_32_1_6945:u32 = -8:u32
dsa_T_t_1_6946:u32 = dsa_R_EAX_32_1_6944:u32
dsa_R_EAX_32_1_6947:u32 = dsa_R_EAX_32_1_6944:u32 - dsa_R_EDI_32_1_6945:u32
dsa_R_CF_1_6948:bool = dsa_T_t_1_6946:u32 < dsa_R_EDI_32_1_6945:u32
dsa_R_OF_1_6949:bool =
  high:bool((dsa_T_t_1_6946:u32 ^ dsa_R_EDI_32_1_6945:u32) &
            (dsa_T_t_1_6946:u32 ^ dsa_R_EAX_32_1_6947:u32))
dsa_R_AF_1_6950:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_6947:u32 ^ dsa_T_t_1_6946:u32 ^ dsa_R_EDI_32_1_6945:u32))
dsa_R_PF_3_6953:bool =
  ~low:bool(let dsa_T_acc_1_6951:u32 :=
                                         dsa_R_EAX_32_1_6947:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_6947:u32 in
            let dsa_T_acc_2_6952:u32 :=
                                         dsa_T_acc_1_6951:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6951:u32 in
            dsa_T_acc_2_6952:u32 >> 1:u32 ^ dsa_T_acc_2_6952:u32)
dsa_R_SF_1_6954:bool = high:bool(dsa_R_EAX_32_1_6947:u32)
dsa_R_ZF_1_6955:bool = 0:u32 == dsa_R_EAX_32_1_6947:u32
addr 0xdcff5ab1 @asm "cmp    ecx,DWORD PTR [ebx+0x164]" @tid "0"
  @context "R_ECX_32" = 0x41414139, -1, u32, rd
  @context "R_EBX_32" = 0xdd06d000, 0, u32, rd
  @context "R_EFLAGS" = 0x296, 0, u32, wr
  @context "mem32[0xdd06d164]" = 0x0, 0, u8, rd
  @context "mem32[0xdd06d165]" = 0x0, 0, u8, rd
  @context "mem32[0xdd06d166]" = 0x10, 0, u8, rd
  @context "mem32[0xdd06d167]" = 0x0, 0, u8, rd
label pc_0xdcff5ab1
dsa_mem_dd06d167_1_6956:u8 = low:u8(0:u8)
dsa_mem_dd06d164_1_6957:u8 = low:u8(0:u8)
dsa_mem_dd06d165_1_6958:u8 = low:u8(0:u8)
dsa_mem_dd06d166_1_6959:u8 = low:u8(0x10:u8)
dsa_R_ZF_1_6960:bool = false
dsa_R_EBX_32_1_6961:u32 = 0xdd06d000:u32
dsa_R_AF_1_6962:bool = true
dsa_R_OF_1_6963:bool = false
dsa_R_SF_1_6964:bool = true
dsa_R_DF_1_6965:bool = false
dsa_R_CF_1_6966:bool = false
dsa_R_EFLAGS_1_6967:u32 = 0x296:u32
dsa_R_PF_1_6968:bool = true
dsa_T_t_1_6969:u32 =
  dsa_R_ECX_32_1_6934:u32 -
  (pad:u32(dsa_mem_dd06d167_1_6956:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_dd06d166_1_6959:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_dd06d165_1_6958:u8) << 8:u32 |
  pad:u32(dsa_mem_dd06d164_1_6957:u8))))
dsa_R_CF_1_6970:bool =
  dsa_R_ECX_32_1_6934:u32 <
  (pad:u32(dsa_mem_dd06d167_1_6956:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_dd06d166_1_6959:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_dd06d165_1_6958:u8) << 8:u32 |
  pad:u32(dsa_mem_dd06d164_1_6957:u8))))
dsa_R_OF_1_6971:bool =
  high:bool((dsa_R_ECX_32_1_6934:u32 ^
            (pad:u32(dsa_mem_dd06d167_1_6956:u8) << 0x18:u32 |
            (pad:u32(dsa_mem_dd06d166_1_6959:u8) << 0x10:u32 |
            (pad:u32(dsa_mem_dd06d165_1_6958:u8) << 8:u32 |
            pad:u32(dsa_mem_dd06d164_1_6957:u8))))) &
            (dsa_R_ECX_32_1_6934:u32 ^ dsa_T_t_1_6969:u32))
dsa_R_AF_1_6972:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_T_t_1_6969:u32 ^ dsa_R_ECX_32_1_6934:u32 ^
  (pad:u32(dsa_mem_dd06d167_1_6956:u8) << 0x18:u32 |
  (pad:u32(dsa_mem_dd06d166_1_6959:u8) << 0x10:u32 |
  (pad:u32(dsa_mem_dd06d165_1_6958:u8) << 8:u32 |
  pad:u32(dsa_mem_dd06d164_1_6957:u8))))))
dsa_R_PF_3_6975:bool =
  ~low:bool(let dsa_T_acc_1_6973:u32 :=
                                         dsa_T_t_1_6969:u32 >> 4:u32 ^
                                         dsa_T_t_1_6969:u32 in
            let dsa_T_acc_2_6974:u32 :=
                                         dsa_T_acc_1_6973:u32 >> 2:u32 ^
                                         dsa_T_acc_1_6973:u32 in
            dsa_T_acc_2_6974:u32 >> 1:u32 ^ dsa_T_acc_2_6974:u32)
dsa_R_SF_1_6976:bool = high:bool(dsa_T_t_1_6969:u32)
dsa_R_ZF_1_6977:bool = 0:u32 == dsa_T_t_1_6969:u32
addr 0xdcff5ab9 @asm "jae    0x00000000dcff6780" @tid "0"
  @context "R_EIP" = 0xdcff5ab9, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff5ab9
dsa_R_DF_1_6978:bool = false
dsa_R_EIP_1_6979:u32 = 0xdcff5ab9:u32
assert ~dsa_R_CF_1_6970:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff6780:u32, "nocjmp168"*/
addr 0xdcff6780 @asm "movdqu xmm1,XMMWORD PTR [eax]" @tid "0"
  @context "R_YMM1" = 0x0, 0, u256, wr
  @context "R_EAX_32" = 0xffaf0724, 0, u32, rd
  @context "mem32[0xffaf0724]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0725]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0726]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0727]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0728]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0729]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf072a]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf072b]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf072c]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf072d]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf072e]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf072f]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0730]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0731]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0732]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0733]" = 0x41, -1, u8, rd
label pc_0xdcff6780
dsa_R_YMM1_1_6980:u256 = 0:u256
dsa_R_EAX_32_1_6981:u32 = 0xffaf0724:u32
dsa_R_YMM1_1_6982:u256 =
  concat:[extract:255:128:[dsa_R_YMM1_1_6980:u256]][
   pad:u128(dsa_mem_ffaf0733_1_2529:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0732_1_2528:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0731_1_2510:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0730_1_2509:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf072f_1_2508:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf072e_1_2507:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf072d_1_2489:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf072c_1_2488:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf072b_1_2487:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf072a_1_2486:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0729_1_2468:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0728_1_2467:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0727_1_2466:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0726_1_2465:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0725_1_2447:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0724_1_2446:u8)))))))))))))))]
addr 0xdcff6784 @asm "movdqu XMMWORD PTR [esi],xmm0" @tid "0"
  @context "R_ESI_32" = 0x8656008, 0, u32, rd
  @context "R_YMM0" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x8656008]" = 0x0, 0, u8, wr
  @context "mem32[0x8656009]" = 0x0, 0, u8, wr
  @context "mem32[0x865600a]" = 0x0, 0, u8, wr
  @context "mem32[0x865600b]" = 0x0, 0, u8, wr
  @context "mem32[0x865600c]" = 0x0, 0, u8, wr
  @context "mem32[0x865600d]" = 0x0, 0, u8, wr
  @context "mem32[0x865600e]" = 0x0, 0, u8, wr
  @context "mem32[0x865600f]" = 0x0, 0, u8, wr
  @context "mem32[0x8656010]" = 0x0, 0, u8, wr
  @context "mem32[0x8656011]" = 0x0, 0, u8, wr
  @context "mem32[0x8656012]" = 0x0, 0, u8, wr
  @context "mem32[0x8656013]" = 0x0, 0, u8, wr
  @context "mem32[0x8656014]" = 0x0, 0, u8, wr
  @context "mem32[0x8656015]" = 0x0, 0, u8, wr
  @context "mem32[0x8656016]" = 0x0, 0, u8, wr
  @context "mem32[0x8656017]" = 0x0, 0, u8, wr
label pc_0xdcff6784
dsa_mem_8656008_1_6983:u8 = low:u8(0:u8)
dsa_mem_8656016_1_6984:u8 = low:u8(0:u8)
dsa_mem_865600d_1_6985:u8 = low:u8(0:u8)
dsa_mem_865600b_1_6986:u8 = low:u8(0:u8)
dsa_mem_8656011_1_6987:u8 = low:u8(0:u8)
dsa_mem_865600c_1_6988:u8 = low:u8(0:u8)
dsa_mem_865600a_1_6989:u8 = low:u8(0:u8)
dsa_mem_8656015_1_6990:u8 = low:u8(0:u8)
dsa_mem_8656013_1_6991:u8 = low:u8(0:u8)
dsa_mem_8656009_1_6992:u8 = low:u8(0:u8)
dsa_mem_8656010_1_6993:u8 = low:u8(0:u8)
dsa_mem_865600e_1_6994:u8 = low:u8(0:u8)
dsa_mem_8656012_1_6995:u8 = low:u8(0:u8)
dsa_mem_865600f_1_6996:u8 = low:u8(0:u8)
dsa_mem_8656014_1_6997:u8 = low:u8(0:u8)
dsa_mem_8656017_1_6998:u8 = low:u8(0:u8)
dsa_R_ESI_32_1_6999:u32 = 0x8656008:u32
dsa_mem_8656008_1_7000:u8 = low:u8(low:u128(dsa_R_YMM0_1_6911:u256))
dsa_mem_8656009_1_7001:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 8:u128)
dsa_mem_865600a_1_7002:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x10:u128)
dsa_mem_865600b_1_7003:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x18:u128)
dsa_mem_865600c_1_7004:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x20:u128)
dsa_mem_865600d_1_7005:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x28:u128)
dsa_mem_865600e_1_7006:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x30:u128)
dsa_mem_865600f_1_7007:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x38:u128)
dsa_mem_8656010_1_7008:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x40:u128)
dsa_mem_8656011_1_7009:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x48:u128)
dsa_mem_8656012_1_7010:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x50:u128)
dsa_mem_8656013_1_7011:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x58:u128)
dsa_mem_8656014_1_7012:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x60:u128)
dsa_mem_8656015_1_7013:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x68:u128)
dsa_mem_8656016_1_7014:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x70:u128)
dsa_mem_8656017_1_7015:u8 =
  low:u8(low:u128(dsa_R_YMM0_1_6911:u256) >> 0x78:u128)
addr 0xdcff6788 @asm "movntdq XMMWORD PTR [edx],xmm1" @tid "0"
  @context "R_EDX_32" = 0x8656010, 0, u32, rd
  @context "R_YMM1" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x8656010]" = 0x41, -1, u8, wr
  @context "mem32[0x8656011]" = 0x41, -1, u8, wr
  @context "mem32[0x8656012]" = 0x41, -1, u8, wr
  @context "mem32[0x8656013]" = 0x41, -1, u8, wr
  @context "mem32[0x8656014]" = 0x41, -1, u8, wr
  @context "mem32[0x8656015]" = 0x41, -1, u8, wr
  @context "mem32[0x8656016]" = 0x41, -1, u8, wr
  @context "mem32[0x8656017]" = 0x41, -1, u8, wr
  @context "mem32[0x8656018]" = 0x0, 0, u8, wr
  @context "mem32[0x8656019]" = 0x0, 0, u8, wr
  @context "mem32[0x865601a]" = 0x0, 0, u8, wr
  @context "mem32[0x865601b]" = 0x0, 0, u8, wr
  @context "mem32[0x865601c]" = 0x0, 0, u8, wr
  @context "mem32[0x865601d]" = 0x0, 0, u8, wr
  @context "mem32[0x865601e]" = 0x0, 0, u8, wr
  @context "mem32[0x865601f]" = 0x0, 0, u8, wr
label pc_0xdcff6788
dsa_mem_865601f_1_7016:u8 = low:u8(0:u8)
dsa_mem_8656018_1_7017:u8 = low:u8(0:u8)
dsa_mem_865601b_1_7018:u8 = low:u8(0:u8)
dsa_mem_865601a_1_7019:u8 = low:u8(0:u8)
dsa_mem_865601c_1_7020:u8 = low:u8(0:u8)
dsa_mem_865601d_1_7021:u8 = low:u8(0:u8)
dsa_mem_865601e_1_7022:u8 = low:u8(0:u8)
dsa_mem_8656019_1_7023:u8 = low:u8(0:u8)
dsa_R_EDX_32_1_7024:u32 = 0x8656010:u32
addr 0xdcff678c @asm "add    eax,0x10" @tid "0"
  @context "R_EAX_32" = 0xffaf0724, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff678c
dsa_R_DF_1_7025:bool = false
dsa_R_EAX_32_1_7026:u32 = 0xffaf0724:u32
dsa_T_t1_1_7027:u32 = dsa_R_EAX_32_1_7026:u32
dsa_T_t2_1_7028:u32 = 0x10:u32
dsa_R_EAX_32_1_7029:u32 = dsa_R_EAX_32_1_7026:u32 + dsa_T_t2_1_7028:u32
dsa_R_CF_1_7030:bool = dsa_R_EAX_32_1_7029:u32 < dsa_T_t1_1_7027:u32
dsa_R_OF_1_7031:bool =
  high:bool((dsa_T_t1_1_7027:u32 ^ ~dsa_T_t2_1_7028:u32) &
            (dsa_T_t1_1_7027:u32 ^ dsa_R_EAX_32_1_7029:u32))
dsa_R_AF_1_7032:bool =
  0x10:u32 ==
  (0x10:u32 &
  (dsa_R_EAX_32_1_7029:u32 ^ dsa_T_t1_1_7027:u32 ^ dsa_T_t2_1_7028:u32))
dsa_R_PF_3_7035:bool =
  ~low:bool(let dsa_T_acc_1_7033:u32 :=
                                         dsa_R_EAX_32_1_7029:u32 >> 4:u32 ^
                                         dsa_R_EAX_32_1_7029:u32 in
            let dsa_T_acc_2_7034:u32 :=
                                         dsa_T_acc_1_7033:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7033:u32 in
            dsa_T_acc_2_7034:u32 >> 1:u32 ^ dsa_T_acc_2_7034:u32)
dsa_R_SF_1_7036:bool = high:bool(dsa_R_EAX_32_1_7029:u32)
dsa_R_ZF_1_7037:bool = 0:u32 == dsa_R_EAX_32_1_7029:u32
addr 0xdcff6792 @asm "sub    ecx,0x10" @tid "0"
  @context "R_ECX_32" = 0x41414139, -1, u32, rw
  @context "R_EFLAGS" = 0x202, 0, u32, wr
label pc_0xdcff6792
dsa_R_ZF_1_7038:bool = false
dsa_R_AF_1_7039:bool = false
dsa_R_OF_1_7040:bool = false
dsa_R_SF_1_7041:bool = false
dsa_R_DF_1_7042:bool = false
dsa_R_CF_1_7043:bool = false
dsa_R_EFLAGS_1_7044:u32 = 0x202:u32
dsa_R_PF_1_7045:bool = false
dsa_T_t_1_7046:u32 = dsa_R_ECX_32_1_6934:u32
dsa_R_ECX_32_1_7047:u32 = dsa_R_ECX_32_1_6934:u32 - 0x10:u32
dsa_R_CF_1_7048:bool = dsa_T_t_1_7046:u32 < 0x10:u32
dsa_R_OF_1_7049:bool =
  high:bool((dsa_T_t_1_7046:u32 ^ 0x10:u32) &
            (dsa_T_t_1_7046:u32 ^ dsa_R_ECX_32_1_7047:u32))
dsa_R_AF_1_7050:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7047:u32 ^ dsa_T_t_1_7046:u32 ^ 0x10:u32))
dsa_R_PF_3_7053:bool =
  ~low:bool(let dsa_T_acc_1_7051:u32 :=
                                         dsa_R_ECX_32_1_7047:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7047:u32 in
            let dsa_T_acc_2_7052:u32 :=
                                         dsa_T_acc_1_7051:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7051:u32 in
            dsa_T_acc_2_7052:u32 >> 1:u32 ^ dsa_T_acc_2_7052:u32)
dsa_R_SF_1_7054:bool = high:bool(dsa_R_ECX_32_1_7047:u32)
dsa_R_ZF_1_7055:bool = 0:u32 == dsa_R_ECX_32_1_7047:u32
addr 0xdcff6795 @asm "cmp    dl,al" @tid "0"
  @context "R_EDX_32" = 0x8656020, 0, u32, rd
  @context "R_EAX_32" = 0xffaf0734, 0, u32, rd
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff6795
dsa_R_DF_1_7056:bool = false
dsa_R_EDX_32_1_7057:u32 = 0x8656020:u32
dsa_R_EAX_32_1_7058:u32 = 0xffaf0734:u32
dsa_T_t_1_7059:u8 =
  low:u8(dsa_R_EDX_32_1_7057:u32) - low:u8(dsa_R_EAX_32_1_7058:u32)
dsa_R_CF_1_7060:bool =
  low:u8(dsa_R_EDX_32_1_7057:u32) < low:u8(dsa_R_EAX_32_1_7058:u32)
dsa_R_OF_1_7061:bool =
  high:bool((low:u8(dsa_R_EDX_32_1_7057:u32) ^
            low:u8(dsa_R_EAX_32_1_7058:u32)) &
            (low:u8(dsa_R_EDX_32_1_7057:u32) ^ dsa_T_t_1_7059:u8))
dsa_R_AF_1_7062:bool =
  0x10:u8 ==
  (0x10:u8 &
  (dsa_T_t_1_7059:u8 ^ low:u8(dsa_R_EDX_32_1_7057:u32) ^
  low:u8(dsa_R_EAX_32_1_7058:u32)))
dsa_R_PF_3_7065:bool =
  ~low:bool(let dsa_T_acc_1_7063:u8 :=
                                        dsa_T_t_1_7059:u8 >> 4:u8 ^
                                        dsa_T_t_1_7059:u8 in
            let dsa_T_acc_2_7064:u8 :=
                                        dsa_T_acc_1_7063:u8 >> 2:u8 ^
                                        dsa_T_acc_1_7063:u8 in
            dsa_T_acc_2_7064:u8 >> 1:u8 ^ dsa_T_acc_2_7064:u8)
dsa_R_SF_1_7066:bool = high:bool(dsa_T_t_1_7059:u8)
dsa_R_ZF_1_7067:bool = 0:u8 == dsa_T_t_1_7059:u8
addr 0xdcff679e @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41414129, -1, u32, rw
  @context "R_EFLAGS" = 0x293, 0, u32, wr
label pc_0xdcff679e
dsa_R_ZF_1_7068:bool = false
dsa_R_AF_1_7069:bool = true
dsa_R_OF_1_7070:bool = false
dsa_R_SF_1_7071:bool = true
dsa_R_DF_1_7072:bool = false
dsa_R_CF_1_7073:bool = true
dsa_R_EFLAGS_1_7074:u32 = 0x293:u32
dsa_R_PF_1_7075:bool = false
dsa_T_t_1_7076:u32 = dsa_R_ECX_32_1_7047:u32
dsa_R_ECX_32_1_7077:u32 = dsa_R_ECX_32_1_7047:u32 - 0x80:u32
dsa_R_CF_1_7078:bool = dsa_T_t_1_7076:u32 < 0x80:u32
dsa_R_OF_1_7079:bool =
  high:bool((dsa_T_t_1_7076:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7076:u32 ^ dsa_R_ECX_32_1_7077:u32))
dsa_R_AF_1_7080:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7077:u32 ^ dsa_T_t_1_7076:u32 ^ 0x80:u32))
dsa_R_PF_3_7083:bool =
  ~low:bool(let dsa_T_acc_1_7081:u32 :=
                                         dsa_R_ECX_32_1_7077:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7077:u32 in
            let dsa_T_acc_2_7082:u32 :=
                                         dsa_T_acc_1_7081:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7081:u32 in
            dsa_T_acc_2_7082:u32 >> 1:u32 ^ dsa_T_acc_2_7082:u32)
dsa_R_SF_1_7084:bool = high:bool(dsa_R_ECX_32_1_7077:u32)
dsa_R_ZF_1_7085:bool = 0:u32 == dsa_R_ECX_32_1_7077:u32
addr 0xdcff67b3 @asm "movdqu xmm0,XMMWORD PTR [eax]" @tid "0"
  @context "R_YMM0" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf0734, 0, u32, rd
  @context "mem32[0xffaf0734]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0735]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0736]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0737]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0738]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0739]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf073a]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf073b]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf073c]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf073d]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf073e]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf073f]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0740]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0741]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0742]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0743]" = 0x41, -1, u8, rd
label pc_0xdcff67b3
dsa_R_EAX_32_1_7086:u32 = 0xffaf0734:u32
dsa_R_YMM0_1_7087:u256 =
  concat:[extract:255:128:[dsa_R_YMM0_1_6911:u256]][
   pad:u128(dsa_mem_ffaf0743_1_2613:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0742_1_2612:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0741_1_2594:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0740_1_2593:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf073f_1_2592:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf073e_1_2591:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf073d_1_2573:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf073c_1_2572:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf073b_1_2571:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf073a_1_2570:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0739_1_2552:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0738_1_2551:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0737_1_2550:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0736_1_2549:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0735_1_2531:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0734_1_2530:u8)))))))))))))))]
addr 0xdcff67b7 @asm "movdqu xmm1,XMMWORD PTR [eax+0x10]" @tid "0"
  @context "R_YMM1" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf0734, 0, u32, rd
  @context "mem32[0xffaf0744]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0745]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0746]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0747]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0748]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0749]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf074a]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf074b]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf074c]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf074d]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf074e]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf074f]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0750]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0751]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0752]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0753]" = 0x41, -1, u8, rd
label pc_0xdcff67b7
dsa_R_EAX_32_1_7088:u32 = 0xffaf0734:u32
dsa_R_YMM1_1_7089:u256 =
  concat:[extract:255:128:[dsa_R_YMM1_1_6982:u256]][
   pad:u128(dsa_mem_ffaf0753_1_2697:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0752_1_2696:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0751_1_2678:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0750_1_2677:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf074f_1_2676:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf074e_1_2675:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf074d_1_2657:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf074c_1_2656:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf074b_1_2655:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf074a_1_2654:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0749_1_2636:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0748_1_2635:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0747_1_2634:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0746_1_2633:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0745_1_2615:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0744_1_2614:u8)))))))))))))))]
addr 0xdcff67bc @asm "movdqu xmm2,XMMWORD PTR [eax+0x20]" @tid "0"
  @context "R_YMM2" = 0x0, 0, u256, wr
  @context "R_EAX_32" = 0xffaf0734, 0, u32, rd
  @context "mem32[0xffaf0754]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0755]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0756]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0757]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0758]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0759]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf075a]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf075b]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf075c]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf075d]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf075e]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf075f]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0760]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0761]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0762]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0763]" = 0x41, -1, u8, rd
label pc_0xdcff67bc
dsa_R_YMM2_1_7090:u256 = 0:u256
dsa_R_EAX_32_1_7091:u32 = 0xffaf0734:u32
dsa_R_YMM2_1_7092:u256 =
  concat:[extract:255:128:[dsa_R_YMM2_1_7090:u256]][
   pad:u128(dsa_mem_ffaf0763_1_2781:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0762_1_2780:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0761_1_2762:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0760_1_2761:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf075f_1_2760:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf075e_1_2759:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf075d_1_2741:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf075c_1_2740:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf075b_1_2739:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf075a_1_2738:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0759_1_2720:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0758_1_2719:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0757_1_2718:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0756_1_2717:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0755_1_2699:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0754_1_2698:u8)))))))))))))))]
addr 0xdcff67c1 @asm "movdqu xmm3,XMMWORD PTR [eax+0x30]" @tid "0"
  @context "R_YMM3" = 0x0, 0, u256, wr
  @context "R_EAX_32" = 0xffaf0734, 0, u32, rd
  @context "mem32[0xffaf0764]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0765]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0766]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0767]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0768]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0769]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf076a]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf076b]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf076c]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf076d]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf076e]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf076f]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0770]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0771]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0772]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0773]" = 0x41, -1, u8, rd
label pc_0xdcff67c1
dsa_R_EAX_32_1_7093:u32 = 0xffaf0734:u32
dsa_R_YMM3_1_7094:u256 = 0:u256
dsa_R_YMM3_1_7095:u256 =
  concat:[extract:255:128:[dsa_R_YMM3_1_7094:u256]][
   pad:u128(dsa_mem_ffaf0773_1_2865:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0772_1_2864:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0771_1_2846:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0770_1_2845:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf076f_1_2844:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf076e_1_2843:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf076d_1_2825:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf076c_1_2824:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf076b_1_2823:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf076a_1_2822:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0769_1_2804:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0768_1_2803:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0767_1_2802:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0766_1_2801:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0765_1_2783:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0764_1_2782:u8)))))))))))))))]
addr 0xdcff67c6 @asm "movdqu xmm4,XMMWORD PTR [eax+0x40]" @tid "0"
  @context "R_YMM4" = 0x0, 0, u256, wr
  @context "R_EAX_32" = 0xffaf0734, 0, u32, rd
  @context "mem32[0xffaf0774]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0775]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0776]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0777]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0778]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0779]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf077a]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf077b]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf077c]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf077d]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf077e]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf077f]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0780]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0781]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0782]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0783]" = 0x41, -1, u8, rd
label pc_0xdcff67c6
dsa_R_EAX_32_1_7096:u32 = 0xffaf0734:u32
dsa_R_YMM4_1_7097:u256 = 0:u256
dsa_R_YMM4_1_7098:u256 =
  concat:[extract:255:128:[dsa_R_YMM4_1_7097:u256]][
   pad:u128(dsa_mem_ffaf0783_1_2949:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0782_1_2948:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0781_1_2930:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0780_1_2929:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf077f_1_2928:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf077e_1_2927:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf077d_1_2909:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf077c_1_2908:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf077b_1_2907:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf077a_1_2906:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0779_1_2888:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0778_1_2887:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0777_1_2886:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0776_1_2885:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0775_1_2867:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0774_1_2866:u8)))))))))))))))]
addr 0xdcff67cb @asm "movdqu xmm5,XMMWORD PTR [eax+0x50]" @tid "0"
  @context "R_YMM5" = 0x0, 0, u256, wr
  @context "R_EAX_32" = 0xffaf0734, 0, u32, rd
  @context "mem32[0xffaf0784]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0785]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0786]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0787]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0788]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0789]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf078a]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf078b]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf078c]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf078d]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf078e]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf078f]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0790]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0791]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0792]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0793]" = 0x41, -1, u8, rd
label pc_0xdcff67cb
dsa_R_YMM5_1_7099:u256 = 0:u256
dsa_R_EAX_32_1_7100:u32 = 0xffaf0734:u32
dsa_R_YMM5_1_7101:u256 =
  concat:[extract:255:128:[dsa_R_YMM5_1_7099:u256]][
   pad:u128(dsa_mem_ffaf0793_1_3033:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0792_1_3032:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0791_1_3014:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0790_1_3013:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf078f_1_3012:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf078e_1_3011:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf078d_1_2993:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf078c_1_2992:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf078b_1_2991:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf078a_1_2990:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0789_1_2972:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0788_1_2971:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0787_1_2970:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0786_1_2969:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0785_1_2951:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0784_1_2950:u8)))))))))))))))]
addr 0xdcff67d0 @asm "movdqu xmm6,XMMWORD PTR [eax+0x60]" @tid "0"
  @context "R_YMM6" = 0x0, 0, u256, wr
  @context "R_EAX_32" = 0xffaf0734, 0, u32, rd
  @context "mem32[0xffaf0794]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0795]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0796]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0797]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0798]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf0799]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf079a]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf079b]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf079c]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf079d]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf079e]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf079f]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07a0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07a1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07a2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07a3]" = 0x41, -1, u8, rd
label pc_0xdcff67d0
dsa_R_YMM6_1_7102:u256 = 0:u256
dsa_R_EAX_32_1_7103:u32 = 0xffaf0734:u32
dsa_R_YMM6_1_7104:u256 =
  concat:[extract:255:128:[dsa_R_YMM6_1_7102:u256]][
   pad:u128(dsa_mem_ffaf07a3_1_3117:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf07a2_1_3116:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf07a1_1_3098:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf07a0_1_3097:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf079f_1_3096:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf079e_1_3095:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf079d_1_3077:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf079c_1_3076:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf079b_1_3075:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf079a_1_3074:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0799_1_3056:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0798_1_3055:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0797_1_3054:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0796_1_3053:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0795_1_3035:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0794_1_3034:u8)))))))))))))))]
addr 0xdcff67d5 @asm "movdqu xmm7,XMMWORD PTR [eax+0x70]" @tid "0"
  @context "R_YMM7" = 0x0, 0, u256, wr
  @context "R_EAX_32" = 0xffaf0734, 0, u32, rd
  @context "mem32[0xffaf07a4]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07a5]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07a6]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07a7]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07a8]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07a9]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07aa]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07ab]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07ac]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07ad]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07ae]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07af]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07b0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07b1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07b2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07b3]" = 0x41, -1, u8, rd
label pc_0xdcff67d5
dsa_R_EAX_32_1_7105:u32 = 0xffaf0734:u32
dsa_R_YMM7_1_7106:u256 = 0:u256
dsa_R_YMM7_1_7107:u256 =
  concat:[extract:255:128:[dsa_R_YMM7_1_7106:u256]][
   pad:u128(dsa_mem_ffaf07b3_1_3201:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf07b2_1_3200:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf07b1_1_3182:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf07b0_1_3181:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf07af_1_3180:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf07ae_1_3179:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf07ad_1_3161:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf07ac_1_3160:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf07ab_1_3159:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf07aa_1_3158:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf07a9_1_3140:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf07a8_1_3139:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf07a7_1_3138:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf07a6_1_3137:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf07a5_1_3119:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf07a4_1_3118:u8)))))))))))))))]
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414140a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7108:bool = false
dsa_T_t_1_7109:u32 = dsa_R_ECX_32_1_7077:u32
dsa_R_ECX_32_1_7110:u32 = dsa_R_ECX_32_1_7077:u32 - 0x80:u32
dsa_R_CF_1_7111:bool = dsa_T_t_1_7109:u32 < 0x80:u32
dsa_R_OF_1_7112:bool =
  high:bool((dsa_T_t_1_7109:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7109:u32 ^ dsa_R_ECX_32_1_7110:u32))
dsa_R_AF_1_7113:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7110:u32 ^ dsa_T_t_1_7109:u32 ^ 0x80:u32))
dsa_R_PF_3_7116:bool =
  ~low:bool(let dsa_T_acc_1_7114:u32 :=
                                         dsa_R_ECX_32_1_7110:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7110:u32 in
            let dsa_T_acc_2_7115:u32 :=
                                         dsa_T_acc_1_7114:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7114:u32 in
            dsa_T_acc_2_7115:u32 >> 1:u32 ^ dsa_T_acc_2_7115:u32)
dsa_R_SF_1_7117:bool = high:bool(dsa_R_ECX_32_1_7110:u32)
dsa_R_ZF_1_7118:bool = 0:u32 == dsa_R_ECX_32_1_7110:u32
addr 0xdcff67e9 @asm "movntdq XMMWORD PTR [edx],xmm0" @tid "0"
  @context "R_EDX_32" = 0x8656020, 0, u32, rd
  @context "R_YMM0" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x8656020]" = 0x0, 0, u8, wr
  @context "mem32[0x8656021]" = 0x0, 0, u8, wr
  @context "mem32[0x8656022]" = 0x0, 0, u8, wr
  @context "mem32[0x8656023]" = 0x0, 0, u8, wr
  @context "mem32[0x8656024]" = 0x0, 0, u8, wr
  @context "mem32[0x8656025]" = 0x0, 0, u8, wr
  @context "mem32[0x8656026]" = 0x0, 0, u8, wr
  @context "mem32[0x8656027]" = 0x0, 0, u8, wr
  @context "mem32[0x8656028]" = 0x0, 0, u8, wr
  @context "mem32[0x8656029]" = 0x0, 0, u8, wr
  @context "mem32[0x865602a]" = 0x0, 0, u8, wr
  @context "mem32[0x865602b]" = 0x0, 0, u8, wr
  @context "mem32[0x865602c]" = 0x0, 0, u8, wr
  @context "mem32[0x865602d]" = 0x0, 0, u8, wr
  @context "mem32[0x865602e]" = 0x0, 0, u8, wr
  @context "mem32[0x865602f]" = 0x0, 0, u8, wr
label pc_0xdcff67e9
dsa_mem_8656020_1_7119:u8 = low:u8(0:u8)
dsa_mem_865602b_1_7120:u8 = low:u8(0:u8)
dsa_mem_8656026_1_7121:u8 = low:u8(0:u8)
dsa_mem_865602f_1_7122:u8 = low:u8(0:u8)
dsa_mem_8656025_1_7123:u8 = low:u8(0:u8)
dsa_mem_8656024_1_7124:u8 = low:u8(0:u8)
dsa_mem_8656022_1_7125:u8 = low:u8(0:u8)
dsa_mem_865602c_1_7126:u8 = low:u8(0:u8)
dsa_mem_8656023_1_7127:u8 = low:u8(0:u8)
dsa_mem_8656021_1_7128:u8 = low:u8(0:u8)
dsa_mem_865602a_1_7129:u8 = low:u8(0:u8)
dsa_mem_8656028_1_7130:u8 = low:u8(0:u8)
dsa_mem_8656029_1_7131:u8 = low:u8(0:u8)
dsa_mem_865602e_1_7132:u8 = low:u8(0:u8)
dsa_mem_8656027_1_7133:u8 = low:u8(0:u8)
dsa_mem_865602d_1_7134:u8 = low:u8(0:u8)
dsa_R_EDX_32_1_7135:u32 = 0x8656020:u32
addr 0xdcff67ed @asm "movntdq XMMWORD PTR [edx+0x10],xmm1" @tid "0"
  @context "R_EDX_32" = 0x8656020, 0, u32, rd
  @context "R_YMM1" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x8656030]" = 0x0, 0, u8, wr
  @context "mem32[0x8656031]" = 0x0, 0, u8, wr
  @context "mem32[0x8656032]" = 0x0, 0, u8, wr
  @context "mem32[0x8656033]" = 0x0, 0, u8, wr
  @context "mem32[0x8656034]" = 0x0, 0, u8, wr
  @context "mem32[0x8656035]" = 0x0, 0, u8, wr
  @context "mem32[0x8656036]" = 0x0, 0, u8, wr
  @context "mem32[0x8656037]" = 0x0, 0, u8, wr
  @context "mem32[0x8656038]" = 0x0, 0, u8, wr
  @context "mem32[0x8656039]" = 0x0, 0, u8, wr
  @context "mem32[0x865603a]" = 0x0, 0, u8, wr
  @context "mem32[0x865603b]" = 0x0, 0, u8, wr
  @context "mem32[0x865603c]" = 0x60, 0, u8, wr
  @context "mem32[0x865603d]" = 0xd9, 0, u8, wr
  @context "mem32[0x865603e]" = 0x6, 0, u8, wr
  @context "mem32[0x865603f]" = 0xdd, 0, u8, wr
label pc_0xdcff67ed
dsa_mem_865603b_1_7136:u8 = low:u8(0:u8)
dsa_mem_8656030_1_7137:u8 = low:u8(0:u8)
dsa_mem_8656033_1_7138:u8 = low:u8(0:u8)
dsa_mem_865603f_1_7139:u8 = low:u8(0xdd:u8)
dsa_mem_8656038_1_7140:u8 = low:u8(0:u8)
dsa_mem_8656036_1_7141:u8 = low:u8(0:u8)
dsa_mem_865603e_1_7142:u8 = low:u8(6:u8)
dsa_mem_8656032_1_7143:u8 = low:u8(0:u8)
dsa_mem_8656037_1_7144:u8 = low:u8(0:u8)
dsa_mem_8656034_1_7145:u8 = low:u8(0:u8)
dsa_mem_865603d_1_7146:u8 = low:u8(0xd9:u8)
dsa_mem_865603a_1_7147:u8 = low:u8(0:u8)
dsa_mem_8656039_1_7148:u8 = low:u8(0:u8)
dsa_mem_8656035_1_7149:u8 = low:u8(0:u8)
dsa_mem_865603c_1_7150:u8 = low:u8(0x60:u8)
dsa_mem_8656031_1_7151:u8 = low:u8(0:u8)
dsa_R_EDX_32_1_7152:u32 = 0x8656020:u32
addr 0xdcff67f2 @asm "movntdq XMMWORD PTR [edx+0x20],xmm2" @tid "0"
  @context "R_EDX_32" = 0x8656020, 0, u32, rd
  @context "R_YMM2" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x8656040]" = 0xff, 0, u8, wr
  @context "mem32[0x8656041]" = 0xff, 0, u8, wr
  @context "mem32[0x8656042]" = 0xff, 0, u8, wr
  @context "mem32[0x8656043]" = 0xff, 0, u8, wr
  @context "mem32[0x8656044]" = 0x0, 0, u8, wr
  @context "mem32[0x8656045]" = 0x0, 0, u8, wr
  @context "mem32[0x8656046]" = 0x0, 0, u8, wr
  @context "mem32[0x8656047]" = 0x0, 0, u8, wr
  @context "mem32[0x8656048]" = 0x0, 0, u8, wr
  @context "mem32[0x8656049]" = 0x0, 0, u8, wr
  @context "mem32[0x865604a]" = 0x0, 0, u8, wr
  @context "mem32[0x865604b]" = 0x0, 0, u8, wr
  @context "mem32[0x865604c]" = 0x0, 0, u8, wr
  @context "mem32[0x865604d]" = 0x0, 0, u8, wr
  @context "mem32[0x865604e]" = 0x0, 0, u8, wr
  @context "mem32[0x865604f]" = 0x0, 0, u8, wr
label pc_0xdcff67f2
dsa_mem_8656046_1_7153:u8 = low:u8(0:u8)
dsa_mem_865604c_1_7154:u8 = low:u8(0:u8)
dsa_mem_8656045_1_7155:u8 = low:u8(0:u8)
dsa_mem_8656047_1_7156:u8 = low:u8(0:u8)
dsa_mem_8656049_1_7157:u8 = low:u8(0:u8)
dsa_mem_8656041_1_7158:u8 = low:u8(-1:u8)
dsa_mem_865604b_1_7159:u8 = low:u8(0:u8)
dsa_mem_865604f_1_7160:u8 = low:u8(0:u8)
dsa_mem_8656043_1_7161:u8 = low:u8(-1:u8)
dsa_mem_865604a_1_7162:u8 = low:u8(0:u8)
dsa_mem_8656044_1_7163:u8 = low:u8(0:u8)
dsa_mem_8656042_1_7164:u8 = low:u8(-1:u8)
dsa_mem_8656040_1_7165:u8 = low:u8(-1:u8)
dsa_mem_8656048_1_7166:u8 = low:u8(0:u8)
dsa_mem_865604e_1_7167:u8 = low:u8(0:u8)
dsa_mem_865604d_1_7168:u8 = low:u8(0:u8)
dsa_R_EDX_32_1_7169:u32 = 0x8656020:u32
addr 0xdcff67f7 @asm "movntdq XMMWORD PTR [edx+0x30],xmm3" @tid "0"
  @context "R_EDX_32" = 0x8656020, 0, u32, rd
  @context "R_YMM3" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x8656050]" = 0xa0, 0, u8, wr
  @context "mem32[0x8656051]" = 0x60, 0, u8, wr
  @context "mem32[0x8656052]" = 0x65, 0, u8, wr
  @context "mem32[0x8656053]" = 0x8, 0, u8, wr
  @context "mem32[0x8656054]" = 0xff, 0, u8, wr
  @context "mem32[0x8656055]" = 0xff, 0, u8, wr
  @context "mem32[0x8656056]" = 0xff, 0, u8, wr
  @context "mem32[0x8656057]" = 0xff, 0, u8, wr
  @context "mem32[0x8656058]" = 0xff, 0, u8, wr
  @context "mem32[0x8656059]" = 0xff, 0, u8, wr
  @context "mem32[0x865605a]" = 0xff, 0, u8, wr
  @context "mem32[0x865605b]" = 0xff, 0, u8, wr
  @context "mem32[0x865605c]" = 0x0, 0, u8, wr
  @context "mem32[0x865605d]" = 0x0, 0, u8, wr
  @context "mem32[0x865605e]" = 0x0, 0, u8, wr
  @context "mem32[0x865605f]" = 0x0, 0, u8, wr
label pc_0xdcff67f7
dsa_mem_8656056_1_7170:u8 = low:u8(-1:u8)
dsa_mem_865605f_1_7171:u8 = low:u8(0:u8)
dsa_mem_8656051_1_7172:u8 = low:u8(0x60:u8)
dsa_mem_8656050_1_7173:u8 = low:u8(0xa0:u8)
dsa_mem_865605c_1_7174:u8 = low:u8(0:u8)
dsa_mem_865605b_1_7175:u8 = low:u8(-1:u8)
dsa_mem_8656055_1_7176:u8 = low:u8(-1:u8)
dsa_mem_8656059_1_7177:u8 = low:u8(-1:u8)
dsa_mem_8656052_1_7178:u8 = low:u8(0x65:u8)
dsa_mem_8656057_1_7179:u8 = low:u8(-1:u8)
dsa_mem_865605a_1_7180:u8 = low:u8(-1:u8)
dsa_mem_865605e_1_7181:u8 = low:u8(0:u8)
dsa_mem_8656054_1_7182:u8 = low:u8(-1:u8)
dsa_mem_8656058_1_7183:u8 = low:u8(-1:u8)
dsa_mem_865605d_1_7184:u8 = low:u8(0:u8)
dsa_mem_8656053_1_7185:u8 = low:u8(8:u8)
dsa_R_EDX_32_1_7186:u32 = 0x8656020:u32
addr 0xdcff67fc @asm "movntdq XMMWORD PTR [edx+0x40],xmm4" @tid "0"
  @context "R_EDX_32" = 0x8656020, 0, u32, rd
  @context "R_YMM4" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x8656060]" = 0xac, 0, u8, wr
  @context "mem32[0x8656061]" = 0x60, 0, u8, wr
  @context "mem32[0x8656062]" = 0x65, 0, u8, wr
  @context "mem32[0x8656063]" = 0x8, 0, u8, wr
  @context "mem32[0x8656064]" = 0x0, 0, u8, wr
  @context "mem32[0x8656065]" = 0x0, 0, u8, wr
  @context "mem32[0x8656066]" = 0x0, 0, u8, wr
  @context "mem32[0x8656067]" = 0x0, 0, u8, wr
  @context "mem32[0x8656068]" = 0x0, 0, u8, wr
  @context "mem32[0x8656069]" = 0x0, 0, u8, wr
  @context "mem32[0x865606a]" = 0x0, 0, u8, wr
  @context "mem32[0x865606b]" = 0x0, 0, u8, wr
  @context "mem32[0x865606c]" = 0x0, 0, u8, wr
  @context "mem32[0x865606d]" = 0x0, 0, u8, wr
  @context "mem32[0x865606e]" = 0x0, 0, u8, wr
  @context "mem32[0x865606f]" = 0x0, 0, u8, wr
label pc_0xdcff67fc
dsa_mem_8656068_1_7187:u8 = low:u8(0:u8)
dsa_mem_865606a_1_7188:u8 = low:u8(0:u8)
dsa_mem_8656065_1_7189:u8 = low:u8(0:u8)
dsa_mem_8656062_1_7190:u8 = low:u8(0x65:u8)
dsa_mem_8656063_1_7191:u8 = low:u8(8:u8)
dsa_mem_8656064_1_7192:u8 = low:u8(0:u8)
dsa_mem_8656067_1_7193:u8 = low:u8(0:u8)
dsa_mem_865606b_1_7194:u8 = low:u8(0:u8)
dsa_mem_865606c_1_7195:u8 = low:u8(0:u8)
dsa_mem_8656069_1_7196:u8 = low:u8(0:u8)
dsa_mem_865606e_1_7197:u8 = low:u8(0:u8)
dsa_mem_8656060_1_7198:u8 = low:u8(0xac:u8)
dsa_mem_8656061_1_7199:u8 = low:u8(0x60:u8)
dsa_mem_8656066_1_7200:u8 = low:u8(0:u8)
dsa_mem_865606d_1_7201:u8 = low:u8(0:u8)
dsa_mem_865606f_1_7202:u8 = low:u8(0:u8)
dsa_R_EDX_32_1_7203:u32 = 0x8656020:u32
addr 0xdcff6801 @asm "movntdq XMMWORD PTR [edx+0x50],xmm5" @tid "0"
  @context "R_EDX_32" = 0x8656020, 0, u32, rd
  @context "R_YMM5" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x8656070]" = 0xff, 0, u8, wr
  @context "mem32[0x8656071]" = 0xff, 0, u8, wr
  @context "mem32[0x8656072]" = 0xff, 0, u8, wr
  @context "mem32[0x8656073]" = 0xff, 0, u8, wr
  @context "mem32[0x8656074]" = 0x0, 0, u8, wr
  @context "mem32[0x8656075]" = 0x0, 0, u8, wr
  @context "mem32[0x8656076]" = 0x0, 0, u8, wr
  @context "mem32[0x8656077]" = 0x0, 0, u8, wr
  @context "mem32[0x8656078]" = 0x0, 0, u8, wr
  @context "mem32[0x8656079]" = 0x0, 0, u8, wr
  @context "mem32[0x865607a]" = 0x0, 0, u8, wr
  @context "mem32[0x865607b]" = 0x0, 0, u8, wr
  @context "mem32[0x865607c]" = 0x0, 0, u8, wr
  @context "mem32[0x865607d]" = 0x0, 0, u8, wr
  @context "mem32[0x865607e]" = 0x0, 0, u8, wr
  @context "mem32[0x865607f]" = 0x0, 0, u8, wr
label pc_0xdcff6801
dsa_mem_8656076_1_7204:u8 = low:u8(0:u8)
dsa_mem_8656075_1_7205:u8 = low:u8(0:u8)
dsa_mem_8656077_1_7206:u8 = low:u8(0:u8)
dsa_mem_8656078_1_7207:u8 = low:u8(0:u8)
dsa_mem_865607d_1_7208:u8 = low:u8(0:u8)
dsa_mem_8656073_1_7209:u8 = low:u8(-1:u8)
dsa_mem_865607c_1_7210:u8 = low:u8(0:u8)
dsa_mem_865607a_1_7211:u8 = low:u8(0:u8)
dsa_mem_865607b_1_7212:u8 = low:u8(0:u8)
dsa_mem_865607e_1_7213:u8 = low:u8(0:u8)
dsa_mem_8656072_1_7214:u8 = low:u8(-1:u8)
dsa_mem_8656079_1_7215:u8 = low:u8(0:u8)
dsa_mem_8656074_1_7216:u8 = low:u8(0:u8)
dsa_mem_8656070_1_7217:u8 = low:u8(-1:u8)
dsa_mem_8656071_1_7218:u8 = low:u8(-1:u8)
dsa_mem_865607f_1_7219:u8 = low:u8(0:u8)
dsa_R_EDX_32_1_7220:u32 = 0x8656020:u32
addr 0xdcff6806 @asm "movntdq XMMWORD PTR [edx+0x60],xmm6" @tid "0"
  @context "R_EDX_32" = 0x8656020, 0, u32, rd
  @context "R_YMM6" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x8656080]" = 0x0, 0, u8, wr
  @context "mem32[0x8656081]" = 0x0, 0, u8, wr
  @context "mem32[0x8656082]" = 0x0, 0, u8, wr
  @context "mem32[0x8656083]" = 0x0, 0, u8, wr
  @context "mem32[0x8656084]" = 0x0, 0, u8, wr
  @context "mem32[0x8656085]" = 0x0, 0, u8, wr
  @context "mem32[0x8656086]" = 0x0, 0, u8, wr
  @context "mem32[0x8656087]" = 0x0, 0, u8, wr
  @context "mem32[0x8656088]" = 0x0, 0, u8, wr
  @context "mem32[0x8656089]" = 0x0, 0, u8, wr
  @context "mem32[0x865608a]" = 0x0, 0, u8, wr
  @context "mem32[0x865608b]" = 0x0, 0, u8, wr
  @context "mem32[0x865608c]" = 0x0, 0, u8, wr
  @context "mem32[0x865608d]" = 0x0, 0, u8, wr
  @context "mem32[0x865608e]" = 0x0, 0, u8, wr
  @context "mem32[0x865608f]" = 0x0, 0, u8, wr
label pc_0xdcff6806
dsa_mem_8656086_1_7221:u8 = low:u8(0:u8)
dsa_mem_865608a_1_7222:u8 = low:u8(0:u8)
dsa_mem_865608b_1_7223:u8 = low:u8(0:u8)
dsa_mem_8656089_1_7224:u8 = low:u8(0:u8)
dsa_mem_8656087_1_7225:u8 = low:u8(0:u8)
dsa_mem_865608f_1_7226:u8 = low:u8(0:u8)
dsa_mem_865608c_1_7227:u8 = low:u8(0:u8)
dsa_mem_8656084_1_7228:u8 = low:u8(0:u8)
dsa_mem_8656080_1_7229:u8 = low:u8(0:u8)
dsa_mem_8656083_1_7230:u8 = low:u8(0:u8)
dsa_mem_8656081_1_7231:u8 = low:u8(0:u8)
dsa_mem_8656085_1_7232:u8 = low:u8(0:u8)
dsa_mem_865608e_1_7233:u8 = low:u8(0:u8)
dsa_mem_865608d_1_7234:u8 = low:u8(0:u8)
dsa_mem_8656082_1_7235:u8 = low:u8(0:u8)
dsa_mem_8656088_1_7236:u8 = low:u8(0:u8)
dsa_R_EDX_32_1_7237:u32 = 0x8656020:u32
addr 0xdcff680b @asm "movntdq XMMWORD PTR [edx+0x70],xmm7" @tid "0"
  @context "R_EDX_32" = 0x8656020, 0, u32, rd
  @context "R_YMM7" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x8656090]" = 0x0, 0, u8, wr
  @context "mem32[0x8656091]" = 0x0, 0, u8, wr
  @context "mem32[0x8656092]" = 0x0, 0, u8, wr
  @context "mem32[0x8656093]" = 0x0, 0, u8, wr
  @context "mem32[0x8656094]" = 0x0, 0, u8, wr
  @context "mem32[0x8656095]" = 0x0, 0, u8, wr
  @context "mem32[0x8656096]" = 0x0, 0, u8, wr
  @context "mem32[0x8656097]" = 0x0, 0, u8, wr
  @context "mem32[0x8656098]" = 0x0, 0, u8, wr
  @context "mem32[0x8656099]" = 0x0, 0, u8, wr
  @context "mem32[0x865609a]" = 0x0, 0, u8, wr
  @context "mem32[0x865609b]" = 0x0, 0, u8, wr
  @context "mem32[0x865609c]" = 0xa0, 0, u8, wr
  @context "mem32[0x865609d]" = 0xca, 0, u8, wr
  @context "mem32[0x865609e]" = 0x6, 0, u8, wr
  @context "mem32[0x865609f]" = 0xdd, 0, u8, wr
label pc_0xdcff680b
dsa_mem_8656094_1_7238:u8 = low:u8(0:u8)
dsa_mem_8656095_1_7239:u8 = low:u8(0:u8)
dsa_mem_865609e_1_7240:u8 = low:u8(6:u8)
dsa_mem_865609c_1_7241:u8 = low:u8(0xa0:u8)
dsa_mem_865609a_1_7242:u8 = low:u8(0:u8)
dsa_mem_8656093_1_7243:u8 = low:u8(0:u8)
dsa_mem_8656090_1_7244:u8 = low:u8(0:u8)
dsa_mem_8656091_1_7245:u8 = low:u8(0:u8)
dsa_mem_865609b_1_7246:u8 = low:u8(0:u8)
dsa_mem_8656092_1_7247:u8 = low:u8(0:u8)
dsa_mem_865609f_1_7248:u8 = low:u8(0xdd:u8)
dsa_mem_8656098_1_7249:u8 = low:u8(0:u8)
dsa_mem_8656096_1_7250:u8 = low:u8(0:u8)
dsa_mem_865609d_1_7251:u8 = low:u8(0xca:u8)
dsa_mem_8656097_1_7252:u8 = low:u8(0:u8)
dsa_mem_8656099_1_7253:u8 = low:u8(0:u8)
dsa_R_EDX_32_1_7254:u32 = 0x8656020:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7255:bool = false
dsa_R_EIP_1_7256:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7111:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp169"*/
addr 0xdcff67b3 @asm "movdqu xmm0,XMMWORD PTR [eax]" @tid "0"
  @context "R_YMM0" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf07b4, 0, u32, rd
  @context "mem32[0xffaf07b4]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07b5]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07b6]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07b7]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07b8]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07b9]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07ba]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07bb]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07bc]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07bd]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07be]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07bf]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07c0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07c1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07c2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07c3]" = 0x41, -1, u8, rd
label pc_0xdcff67b3
dsa_R_EAX_32_1_7257:u32 = 0xffaf07b4:u32
dsa_R_YMM0_1_7258:u256 =
  concat:[extract:255:128:[dsa_R_YMM0_1_7087:u256]][
   pad:u128(dsa_mem_ffaf07c3_1_3285:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf07c2_1_3284:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf07c1_1_3266:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf07c0_1_3265:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf07bf_1_3264:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf07be_1_3263:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf07bd_1_3245:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf07bc_1_3244:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf07bb_1_3243:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf07ba_1_3242:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf07b9_1_3224:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf07b8_1_3223:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf07b7_1_3222:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf07b6_1_3221:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf07b5_1_3203:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf07b4_1_3202:u8)))))))))))))))]
addr 0xdcff67b7 @asm "movdqu xmm1,XMMWORD PTR [eax+0x10]" @tid "0"
  @context "R_YMM1" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf07b4, 0, u32, rd
  @context "mem32[0xffaf07c4]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07c5]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07c6]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07c7]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07c8]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07c9]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07ca]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07cb]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07cc]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07cd]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07ce]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07cf]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07d0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07d1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07d2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07d3]" = 0x41, -1, u8, rd
label pc_0xdcff67b7
dsa_R_EAX_32_1_7259:u32 = 0xffaf07b4:u32
dsa_R_YMM1_1_7260:u256 =
  concat:[extract:255:128:[dsa_R_YMM1_1_7089:u256]][
   pad:u128(dsa_mem_ffaf07d3_1_3369:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf07d2_1_3368:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf07d1_1_3350:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf07d0_1_3349:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf07cf_1_3348:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf07ce_1_3347:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf07cd_1_3329:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf07cc_1_3328:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf07cb_1_3327:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf07ca_1_3326:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf07c9_1_3308:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf07c8_1_3307:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf07c7_1_3306:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf07c6_1_3305:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf07c5_1_3287:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf07c4_1_3286:u8)))))))))))))))]
addr 0xdcff67bc @asm "movdqu xmm2,XMMWORD PTR [eax+0x20]" @tid "0"
  @context "R_YMM2" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf07b4, 0, u32, rd
  @context "mem32[0xffaf07d4]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07d5]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07d6]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07d7]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07d8]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07d9]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07da]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07db]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07dc]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07dd]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07de]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07df]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07e0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07e1]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07e2]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07e3]" = 0x41, -1, u8, rd
label pc_0xdcff67bc
dsa_R_EAX_32_1_7261:u32 = 0xffaf07b4:u32
dsa_R_YMM2_1_7262:u256 =
  concat:[extract:255:128:[dsa_R_YMM2_1_7092:u256]][
   pad:u128(dsa_mem_ffaf07e3_1_3453:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf07e2_1_3452:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf07e1_1_3434:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf07e0_1_3433:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf07df_1_3432:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf07de_1_3431:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf07dd_1_3413:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf07dc_1_3412:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf07db_1_3411:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf07da_1_3410:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf07d9_1_3392:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf07d8_1_3391:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf07d7_1_3390:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf07d6_1_3389:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf07d5_1_3371:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf07d4_1_3370:u8)))))))))))))))]
addr 0xdcff67c1 @asm "movdqu xmm3,XMMWORD PTR [eax+0x30]" @tid "0"
  @context "R_YMM3" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf07b4, 0, u32, rd
  @context "mem32[0xffaf07e4]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07e5]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07e6]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07e7]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07e8]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07e9]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07ea]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07eb]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07ec]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07ed]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07ee]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07ef]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07f0]" = 0x41, -1, u8, rd
  @context "mem32[0xffaf07f1]" = 0xa, -1, u8, rd
  @context "mem32[0xffaf07f2]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf07f3]" = 0x0, 0, u8, rd
label pc_0xdcff67c1
dsa_mem_ffaf07f2_1_7263:u8 = low:u8(0:u8)
dsa_mem_ffaf07f3_1_7264:u8 = low:u8(0:u8)
dsa_R_EAX_32_1_7265:u32 = 0xffaf07b4:u32
dsa_R_YMM3_1_7266:u256 =
  concat:[extract:255:128:[dsa_R_YMM3_1_7095:u256]][
   pad:u128(dsa_mem_ffaf07f3_1_7264:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf07f2_1_7263:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf07f1_1_3518:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf07f0_1_3517:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf07ef_1_3516:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf07ee_1_3515:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf07ed_1_3497:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf07ec_1_3496:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf07eb_1_3495:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf07ea_1_3494:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf07e9_1_3476:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf07e8_1_3475:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf07e7_1_3474:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf07e6_1_3473:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf07e5_1_3455:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf07e4_1_3454:u8)))))))))))))))]
addr 0xdcff67c6 @asm "movdqu xmm4,XMMWORD PTR [eax+0x40]" @tid "0"
  @context "R_YMM4" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf07b4, 0, u32, rd
  @context "mem32[0xffaf07f4]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf07f5]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf07f6]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf07f7]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf07f8]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf07f9]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf07fa]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf07fb]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf07fc]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf07fd]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf07fe]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf07ff]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0800]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0801]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0802]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0803]" = 0x0, 0, u8, rd
label pc_0xdcff67c6
dsa_mem_ffaf07fd_1_7267:u8 = low:u8(0:u8)
dsa_mem_ffaf07fb_1_7268:u8 = low:u8(0:u8)
dsa_mem_ffaf07fa_1_7269:u8 = low:u8(0:u8)
dsa_mem_ffaf0802_1_7270:u8 = low:u8(0:u8)
dsa_mem_ffaf0800_1_7271:u8 = low:u8(0:u8)
dsa_mem_ffaf0803_1_7272:u8 = low:u8(0:u8)
dsa_mem_ffaf07f6_1_7273:u8 = low:u8(0:u8)
dsa_mem_ffaf07f8_1_7274:u8 = low:u8(0:u8)
dsa_mem_ffaf07f7_1_7275:u8 = low:u8(0:u8)
dsa_mem_ffaf07fc_1_7276:u8 = low:u8(0:u8)
dsa_mem_ffaf07ff_1_7277:u8 = low:u8(0:u8)
dsa_mem_ffaf07fe_1_7278:u8 = low:u8(0:u8)
dsa_mem_ffaf07f9_1_7279:u8 = low:u8(0:u8)
dsa_mem_ffaf0801_1_7280:u8 = low:u8(0:u8)
dsa_mem_ffaf07f4_1_7281:u8 = low:u8(0:u8)
dsa_mem_ffaf07f5_1_7282:u8 = low:u8(0:u8)
dsa_R_EAX_32_1_7283:u32 = 0xffaf07b4:u32
dsa_R_YMM4_1_7284:u256 =
  concat:[extract:255:128:[dsa_R_YMM4_1_7098:u256]][
   pad:u128(dsa_mem_ffaf0803_1_7272:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0802_1_7270:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0801_1_7280:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0800_1_7271:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf07ff_1_7277:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf07fe_1_7278:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf07fd_1_7267:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf07fc_1_7276:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf07fb_1_7268:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf07fa_1_7269:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf07f9_1_7279:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf07f8_1_7274:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf07f7_1_7275:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf07f6_1_7273:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf07f5_1_7282:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf07f4_1_7281:u8)))))))))))))))]
addr 0xdcff67cb @asm "movdqu xmm5,XMMWORD PTR [eax+0x50]" @tid "0"
  @context "R_YMM5" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf07b4, 0, u32, rd
  @context "mem32[0xffaf0804]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0805]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0806]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0807]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0808]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0809]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf080a]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf080b]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf080c]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf080d]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf080e]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf080f]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0810]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0811]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0812]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0813]" = 0x0, 0, u8, rd
label pc_0xdcff67cb
dsa_mem_ffaf0807_1_7285:u8 = low:u8(0:u8)
dsa_mem_ffaf0812_1_7286:u8 = low:u8(0:u8)
dsa_mem_ffaf0805_1_7287:u8 = low:u8(0:u8)
dsa_mem_ffaf080f_1_7288:u8 = low:u8(0:u8)
dsa_mem_ffaf080c_1_7289:u8 = low:u8(0:u8)
dsa_mem_ffaf0809_1_7290:u8 = low:u8(0:u8)
dsa_mem_ffaf0810_1_7291:u8 = low:u8(0:u8)
dsa_mem_ffaf080a_1_7292:u8 = low:u8(0:u8)
dsa_mem_ffaf0808_1_7293:u8 = low:u8(0:u8)
dsa_mem_ffaf080e_1_7294:u8 = low:u8(0:u8)
dsa_mem_ffaf080d_1_7295:u8 = low:u8(0:u8)
dsa_mem_ffaf0811_1_7296:u8 = low:u8(0:u8)
dsa_mem_ffaf080b_1_7297:u8 = low:u8(0:u8)
dsa_mem_ffaf0806_1_7298:u8 = low:u8(0:u8)
dsa_mem_ffaf0804_1_7299:u8 = low:u8(0:u8)
dsa_mem_ffaf0813_1_7300:u8 = low:u8(0:u8)
dsa_R_EAX_32_1_7301:u32 = 0xffaf07b4:u32
dsa_R_YMM5_1_7302:u256 =
  concat:[extract:255:128:[dsa_R_YMM5_1_7101:u256]][
   pad:u128(dsa_mem_ffaf0813_1_7300:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0812_1_7286:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0811_1_7296:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0810_1_7291:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf080f_1_7288:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf080e_1_7294:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf080d_1_7295:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf080c_1_7289:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf080b_1_7297:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf080a_1_7292:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0809_1_7290:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0808_1_7293:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0807_1_7285:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0806_1_7298:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0805_1_7287:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0804_1_7299:u8)))))))))))))))]
addr 0xdcff67d0 @asm "movdqu xmm6,XMMWORD PTR [eax+0x60]" @tid "0"
  @context "R_YMM6" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf07b4, 0, u32, rd
  @context "mem32[0xffaf0814]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0815]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0816]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0817]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0818]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0819]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf081a]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf081b]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf081c]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf081d]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf081e]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf081f]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0820]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0821]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0822]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0823]" = 0x0, 0, u8, rd
label pc_0xdcff67d0
dsa_mem_ffaf0816_1_7303:u8 = low:u8(0:u8)
dsa_mem_ffaf081c_1_7304:u8 = low:u8(0:u8)
dsa_mem_ffaf081e_1_7305:u8 = low:u8(0:u8)
dsa_mem_ffaf081f_1_7306:u8 = low:u8(0:u8)
dsa_mem_ffaf081d_1_7307:u8 = low:u8(0:u8)
dsa_mem_ffaf0821_1_7308:u8 = low:u8(0:u8)
dsa_mem_ffaf0818_1_7309:u8 = low:u8(0:u8)
dsa_mem_ffaf0817_1_7310:u8 = low:u8(0:u8)
dsa_mem_ffaf0815_1_7311:u8 = low:u8(0:u8)
dsa_mem_ffaf0823_1_7312:u8 = low:u8(0:u8)
dsa_mem_ffaf0814_1_7313:u8 = low:u8(0:u8)
dsa_mem_ffaf0820_1_7314:u8 = low:u8(0:u8)
dsa_mem_ffaf0822_1_7315:u8 = low:u8(0:u8)
dsa_mem_ffaf081a_1_7316:u8 = low:u8(0:u8)
dsa_mem_ffaf081b_1_7317:u8 = low:u8(0:u8)
dsa_mem_ffaf0819_1_7318:u8 = low:u8(0:u8)
dsa_R_EAX_32_1_7319:u32 = 0xffaf07b4:u32
dsa_R_YMM6_1_7320:u256 =
  concat:[extract:255:128:[dsa_R_YMM6_1_7104:u256]][
   pad:u128(dsa_mem_ffaf0823_1_7312:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0822_1_7315:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0821_1_7308:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0820_1_7314:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf081f_1_7306:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf081e_1_7305:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf081d_1_7307:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf081c_1_7304:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf081b_1_7317:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf081a_1_7316:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0819_1_7318:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0818_1_7309:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0817_1_7310:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0816_1_7303:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0815_1_7311:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0814_1_7313:u8)))))))))))))))]
addr 0xdcff67d5 @asm "movdqu xmm7,XMMWORD PTR [eax+0x70]" @tid "0"
  @context "R_YMM7" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf07b4, 0, u32, rd
  @context "mem32[0xffaf0824]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0825]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0826]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0827]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0828]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0829]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf082a]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf082b]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf082c]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf082d]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf082e]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf082f]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0830]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0831]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0832]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0833]" = 0x0, 0, u8, rd
label pc_0xdcff67d5
dsa_mem_ffaf082d_1_7321:u8 = low:u8(0:u8)
dsa_mem_ffaf082b_1_7322:u8 = low:u8(0:u8)
dsa_mem_ffaf082c_1_7323:u8 = low:u8(0:u8)
dsa_mem_ffaf082e_1_7324:u8 = low:u8(0:u8)
dsa_mem_ffaf0832_1_7325:u8 = low:u8(0:u8)
dsa_mem_ffaf082a_1_7326:u8 = low:u8(0:u8)
dsa_mem_ffaf0830_1_7327:u8 = low:u8(0:u8)
dsa_mem_ffaf0831_1_7328:u8 = low:u8(0:u8)
dsa_mem_ffaf0833_1_7329:u8 = low:u8(0:u8)
dsa_mem_ffaf0829_1_7330:u8 = low:u8(0:u8)
dsa_mem_ffaf0827_1_7331:u8 = low:u8(0:u8)
dsa_mem_ffaf0825_1_7332:u8 = low:u8(0:u8)
dsa_mem_ffaf0828_1_7333:u8 = low:u8(0:u8)
dsa_mem_ffaf0824_1_7334:u8 = low:u8(0:u8)
dsa_mem_ffaf0826_1_7335:u8 = low:u8(0:u8)
dsa_mem_ffaf082f_1_7336:u8 = low:u8(0:u8)
dsa_R_EAX_32_1_7337:u32 = 0xffaf07b4:u32
dsa_R_YMM7_1_7338:u256 =
  concat:[extract:255:128:[dsa_R_YMM7_1_7107:u256]][
   pad:u128(dsa_mem_ffaf0833_1_7329:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0832_1_7325:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0831_1_7328:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0830_1_7327:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf082f_1_7336:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf082e_1_7324:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf082d_1_7321:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf082c_1_7323:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf082b_1_7322:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf082a_1_7326:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0829_1_7330:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0828_1_7333:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0827_1_7331:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0826_1_7335:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0825_1_7332:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0824_1_7334:u8)))))))))))))))]
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41414029, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7339:bool = false
dsa_T_t_1_7340:u32 = dsa_R_ECX_32_1_7110:u32
dsa_R_ECX_32_1_7341:u32 = dsa_R_ECX_32_1_7110:u32 - 0x80:u32
dsa_R_CF_1_7342:bool = dsa_T_t_1_7340:u32 < 0x80:u32
dsa_R_OF_1_7343:bool =
  high:bool((dsa_T_t_1_7340:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7340:u32 ^ dsa_R_ECX_32_1_7341:u32))
dsa_R_AF_1_7344:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7341:u32 ^ dsa_T_t_1_7340:u32 ^ 0x80:u32))
dsa_R_PF_3_7347:bool =
  ~low:bool(let dsa_T_acc_1_7345:u32 :=
                                         dsa_R_ECX_32_1_7341:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7341:u32 in
            let dsa_T_acc_2_7346:u32 :=
                                         dsa_T_acc_1_7345:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7345:u32 in
            dsa_T_acc_2_7346:u32 >> 1:u32 ^ dsa_T_acc_2_7346:u32)
dsa_R_SF_1_7348:bool = high:bool(dsa_R_ECX_32_1_7341:u32)
dsa_R_ZF_1_7349:bool = 0:u32 == dsa_R_ECX_32_1_7341:u32
addr 0xdcff67e9 @asm "movntdq XMMWORD PTR [edx],xmm0" @tid "0"
  @context "R_EDX_32" = 0x86560a0, 0, u32, rd
  @context "R_YMM0" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x86560a0]" = 0x0, 0, u8, wr
  @context "mem32[0x86560a1]" = 0x0, 0, u8, wr
  @context "mem32[0x86560a2]" = 0x0, 0, u8, wr
  @context "mem32[0x86560a3]" = 0x0, 0, u8, wr
  @context "mem32[0x86560a4]" = 0x0, 0, u8, wr
  @context "mem32[0x86560a5]" = 0x0, 0, u8, wr
  @context "mem32[0x86560a6]" = 0x0, 0, u8, wr
  @context "mem32[0x86560a7]" = 0x0, 0, u8, wr
  @context "mem32[0x86560a8]" = 0x0, 0, u8, wr
  @context "mem32[0x86560a9]" = 0x0, 0, u8, wr
  @context "mem32[0x86560aa]" = 0x0, 0, u8, wr
  @context "mem32[0x86560ab]" = 0x0, 0, u8, wr
  @context "mem32[0x86560ac]" = 0x0, 0, u8, wr
  @context "mem32[0x86560ad]" = 0x0, 0, u8, wr
  @context "mem32[0x86560ae]" = 0x0, 0, u8, wr
  @context "mem32[0x86560af]" = 0x0, 0, u8, wr
label pc_0xdcff67e9
dsa_mem_86560aa_1_7350:u8 = low:u8(0:u8)
dsa_mem_86560a3_1_7351:u8 = low:u8(0:u8)
dsa_mem_86560a4_1_7352:u8 = low:u8(0:u8)
dsa_mem_86560ae_1_7353:u8 = low:u8(0:u8)
dsa_mem_86560ac_1_7354:u8 = low:u8(0:u8)
dsa_mem_86560ad_1_7355:u8 = low:u8(0:u8)
dsa_mem_86560a8_1_7356:u8 = low:u8(0:u8)
dsa_mem_86560a1_1_7357:u8 = low:u8(0:u8)
dsa_mem_86560a5_1_7358:u8 = low:u8(0:u8)
dsa_mem_86560a0_1_7359:u8 = low:u8(0:u8)
dsa_mem_86560a6_1_7360:u8 = low:u8(0:u8)
dsa_mem_86560ab_1_7361:u8 = low:u8(0:u8)
dsa_mem_86560a9_1_7362:u8 = low:u8(0:u8)
dsa_mem_86560a2_1_7363:u8 = low:u8(0:u8)
dsa_mem_86560af_1_7364:u8 = low:u8(0:u8)
dsa_mem_86560a7_1_7365:u8 = low:u8(0:u8)
dsa_R_EDX_32_1_7366:u32 = 0x86560a0:u32
addr 0xdcff67ed @asm "movntdq XMMWORD PTR [edx+0x10],xmm1" @tid "0"
  @context "R_EDX_32" = 0x86560a0, 0, u32, rd
  @context "R_YMM1" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x86560b0]" = 0x0, 0, u8, wr
  @context "mem32[0x86560b1]" = 0x0, 0, u8, wr
  @context "mem32[0x86560b2]" = 0x0, 0, u8, wr
  @context "mem32[0x86560b3]" = 0x0, 0, u8, wr
  @context "mem32[0x86560b4]" = 0x0, 0, u8, wr
  @context "mem32[0x86560b5]" = 0x0, 0, u8, wr
  @context "mem32[0x86560b6]" = 0x0, 0, u8, wr
  @context "mem32[0x86560b7]" = 0x0, 0, u8, wr
  @context "mem32[0x86560b8]" = 0x0, 0, u8, wr
  @context "mem32[0x86560b9]" = 0x0, 0, u8, wr
  @context "mem32[0x86560ba]" = 0x0, 0, u8, wr
  @context "mem32[0x86560bb]" = 0x0, 0, u8, wr
  @context "mem32[0x86560bc]" = 0x0, 0, u8, wr
  @context "mem32[0x86560bd]" = 0x0, 0, u8, wr
  @context "mem32[0x86560be]" = 0x0, 0, u8, wr
  @context "mem32[0x86560bf]" = 0x0, 0, u8, wr
label pc_0xdcff67ed
dsa_mem_86560b8_1_7367:u8 = low:u8(0:u8)
dsa_mem_86560b9_1_7368:u8 = low:u8(0:u8)
dsa_mem_86560b6_1_7369:u8 = low:u8(0:u8)
dsa_mem_86560be_1_7370:u8 = low:u8(0:u8)
dsa_mem_86560b7_1_7371:u8 = low:u8(0:u8)
dsa_mem_86560ba_1_7372:u8 = low:u8(0:u8)
dsa_mem_86560bc_1_7373:u8 = low:u8(0:u8)
dsa_mem_86560bd_1_7374:u8 = low:u8(0:u8)
dsa_mem_86560bf_1_7375:u8 = low:u8(0:u8)
dsa_mem_86560bb_1_7376:u8 = low:u8(0:u8)
dsa_mem_86560b1_1_7377:u8 = low:u8(0:u8)
dsa_mem_86560b4_1_7378:u8 = low:u8(0:u8)
dsa_mem_86560b2_1_7379:u8 = low:u8(0:u8)
dsa_mem_86560b0_1_7380:u8 = low:u8(0:u8)
dsa_mem_86560b5_1_7381:u8 = low:u8(0:u8)
dsa_mem_86560b3_1_7382:u8 = low:u8(0:u8)
dsa_R_EDX_32_1_7383:u32 = 0x86560a0:u32
addr 0xdcff67f2 @asm "movntdq XMMWORD PTR [edx+0x20],xmm2" @tid "0"
  @context "R_EDX_32" = 0x86560a0, 0, u32, rd
  @context "R_YMM2" = 0x41414141414141414141414141414141, -1, u256, rd
  @context "mem32[0x86560c0]" = 0x0, 0, u8, wr
  @context "mem32[0x86560c1]" = 0x0, 0, u8, wr
  @context "mem32[0x86560c2]" = 0x0, 0, u8, wr
  @context "mem32[0x86560c3]" = 0x0, 0, u8, wr
  @context "mem32[0x86560c4]" = 0x0, 0, u8, wr
  @context "mem32[0x86560c5]" = 0x0, 0, u8, wr
  @context "mem32[0x86560c6]" = 0x0, 0, u8, wr
  @context "mem32[0x86560c7]" = 0x0, 0, u8, wr
  @context "mem32[0x86560c8]" = 0x0, 0, u8, wr
  @context "mem32[0x86560c9]" = 0x0, 0, u8, wr
  @context "mem32[0x86560ca]" = 0x0, 0, u8, wr
  @context "mem32[0x86560cb]" = 0x0, 0, u8, wr
  @context "mem32[0x86560cc]" = 0x0, 0, u8, wr
  @context "mem32[0x86560cd]" = 0x0, 0, u8, wr
  @context "mem32[0x86560ce]" = 0x0, 0, u8, wr
  @context "mem32[0x86560cf]" = 0x0, 0, u8, wr
label pc_0xdcff67f2
dsa_mem_86560c7_1_7384:u8 = low:u8(0:u8)
dsa_mem_86560c2_1_7385:u8 = low:u8(0:u8)
dsa_mem_86560c3_1_7386:u8 = low:u8(0:u8)
dsa_mem_86560c8_1_7387:u8 = low:u8(0:u8)
dsa_mem_86560c9_1_7388:u8 = low:u8(0:u8)
dsa_mem_86560cc_1_7389:u8 = low:u8(0:u8)
dsa_mem_86560cf_1_7390:u8 = low:u8(0:u8)
dsa_mem_86560cb_1_7391:u8 = low:u8(0:u8)
dsa_mem_86560c1_1_7392:u8 = low:u8(0:u8)
dsa_mem_86560c6_1_7393:u8 = low:u8(0:u8)
dsa_mem_86560cd_1_7394:u8 = low:u8(0:u8)
dsa_mem_86560c0_1_7395:u8 = low:u8(0:u8)
dsa_mem_86560ca_1_7396:u8 = low:u8(0:u8)
dsa_mem_86560c5_1_7397:u8 = low:u8(0:u8)
dsa_mem_86560c4_1_7398:u8 = low:u8(0:u8)
dsa_mem_86560ce_1_7399:u8 = low:u8(0:u8)
dsa_R_EDX_32_1_7400:u32 = 0x86560a0:u32
addr 0xdcff67f7 @asm "movntdq XMMWORD PTR [edx+0x30],xmm3" @tid "0"
  @context "R_EDX_32" = 0x86560a0, 0, u32, rd
  @context "R_YMM3" = 0xa41414141414141414141414141, -1, u256, rd
  @context "mem32[0x86560d0]" = 0x0, 0, u8, wr
  @context "mem32[0x86560d1]" = 0x0, 0, u8, wr
  @context "mem32[0x86560d2]" = 0x0, 0, u8, wr
  @context "mem32[0x86560d3]" = 0x0, 0, u8, wr
  @context "mem32[0x86560d4]" = 0x0, 0, u8, wr
  @context "mem32[0x86560d5]" = 0x0, 0, u8, wr
  @context "mem32[0x86560d6]" = 0x0, 0, u8, wr
  @context "mem32[0x86560d7]" = 0x0, 0, u8, wr
  @context "mem32[0x86560d8]" = 0x0, 0, u8, wr
  @context "mem32[0x86560d9]" = 0x0, 0, u8, wr
  @context "mem32[0x86560da]" = 0x0, 0, u8, wr
  @context "mem32[0x86560db]" = 0x0, 0, u8, wr
  @context "mem32[0x86560dc]" = 0x0, 0, u8, wr
  @context "mem32[0x86560dd]" = 0x0, 0, u8, wr
  @context "mem32[0x86560de]" = 0x0, 0, u8, wr
  @context "mem32[0x86560df]" = 0x0, 0, u8, wr
label pc_0xdcff67f7
dsa_mem_86560de_1_7401:u8 = low:u8(0:u8)
dsa_mem_86560df_1_7402:u8 = low:u8(0:u8)
dsa_mem_86560d3_1_7403:u8 = low:u8(0:u8)
dsa_mem_86560d2_1_7404:u8 = low:u8(0:u8)
dsa_mem_86560d8_1_7405:u8 = low:u8(0:u8)
dsa_mem_86560d4_1_7406:u8 = low:u8(0:u8)
dsa_mem_86560d7_1_7407:u8 = low:u8(0:u8)
dsa_mem_86560d5_1_7408:u8 = low:u8(0:u8)
dsa_mem_86560d0_1_7409:u8 = low:u8(0:u8)
dsa_mem_86560db_1_7410:u8 = low:u8(0:u8)
dsa_mem_86560d6_1_7411:u8 = low:u8(0:u8)
dsa_mem_86560dc_1_7412:u8 = low:u8(0:u8)
dsa_mem_86560d9_1_7413:u8 = low:u8(0:u8)
dsa_mem_86560d1_1_7414:u8 = low:u8(0:u8)
dsa_mem_86560da_1_7415:u8 = low:u8(0:u8)
dsa_mem_86560dd_1_7416:u8 = low:u8(0:u8)
dsa_R_EDX_32_1_7417:u32 = 0x86560a0:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7418:bool = false
dsa_R_EIP_1_7419:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7342:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp170"*/
addr 0xdcff67b3 @asm "movdqu xmm0,XMMWORD PTR [eax]" @tid "0"
  @context "R_YMM0" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf0834, 0, u32, rd
  @context "mem32[0xffaf0834]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0835]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0836]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0837]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0838]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0839]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf083a]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf083b]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf083c]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf083d]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf083e]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf083f]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0840]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0841]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0842]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0843]" = 0x0, 0, u8, rd
label pc_0xdcff67b3
dsa_mem_ffaf0836_1_7420:u8 = low:u8(0:u8)
dsa_mem_ffaf083f_1_7421:u8 = low:u8(0:u8)
dsa_mem_ffaf0839_1_7422:u8 = low:u8(0:u8)
dsa_mem_ffaf083e_1_7423:u8 = low:u8(0:u8)
dsa_mem_ffaf0842_1_7424:u8 = low:u8(0:u8)
dsa_mem_ffaf0841_1_7425:u8 = low:u8(0:u8)
dsa_mem_ffaf0834_1_7426:u8 = low:u8(0:u8)
dsa_mem_ffaf0837_1_7427:u8 = low:u8(0:u8)
dsa_mem_ffaf0838_1_7428:u8 = low:u8(0:u8)
dsa_mem_ffaf083b_1_7429:u8 = low:u8(0:u8)
dsa_mem_ffaf0840_1_7430:u8 = low:u8(0:u8)
dsa_mem_ffaf083a_1_7431:u8 = low:u8(0:u8)
dsa_mem_ffaf0835_1_7432:u8 = low:u8(0:u8)
dsa_mem_ffaf083d_1_7433:u8 = low:u8(0:u8)
dsa_mem_ffaf083c_1_7434:u8 = low:u8(0:u8)
dsa_mem_ffaf0843_1_7435:u8 = low:u8(0:u8)
dsa_R_EAX_32_1_7436:u32 = 0xffaf0834:u32
dsa_R_YMM0_1_7437:u256 =
  concat:[extract:255:128:[dsa_R_YMM0_1_7258:u256]][
   pad:u128(dsa_mem_ffaf0843_1_7435:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0842_1_7424:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0841_1_7425:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0840_1_7430:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf083f_1_7421:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf083e_1_7423:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf083d_1_7433:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf083c_1_7434:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf083b_1_7429:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf083a_1_7431:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0839_1_7422:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0838_1_7428:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0837_1_7427:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0836_1_7420:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0835_1_7432:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0834_1_7426:u8)))))))))))))))]
addr 0xdcff67b7 @asm "movdqu xmm1,XMMWORD PTR [eax+0x10]" @tid "0"
  @context "R_YMM1" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf0834, 0, u32, rd
  @context "mem32[0xffaf0844]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0845]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0846]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0847]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0848]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0849]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf084a]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf084b]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf084c]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf084d]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf084e]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf084f]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0850]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0851]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0852]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0853]" = 0x0, 0, u8, rd
label pc_0xdcff67b7
dsa_mem_ffaf084b_1_7438:u8 = low:u8(0:u8)
dsa_mem_ffaf084f_1_7439:u8 = low:u8(0:u8)
dsa_mem_ffaf0852_1_7440:u8 = low:u8(0:u8)
dsa_mem_ffaf0850_1_7441:u8 = low:u8(0:u8)
dsa_mem_ffaf0853_1_7442:u8 = low:u8(0:u8)
dsa_mem_ffaf0844_1_7443:u8 = low:u8(0:u8)
dsa_mem_ffaf084d_1_7444:u8 = low:u8(0:u8)
dsa_mem_ffaf084a_1_7445:u8 = low:u8(0:u8)
dsa_mem_ffaf0849_1_7446:u8 = low:u8(0:u8)
dsa_mem_ffaf084c_1_7447:u8 = low:u8(0:u8)
dsa_mem_ffaf0847_1_7448:u8 = low:u8(0:u8)
dsa_mem_ffaf084e_1_7449:u8 = low:u8(0:u8)
dsa_mem_ffaf0845_1_7450:u8 = low:u8(0:u8)
dsa_mem_ffaf0846_1_7451:u8 = low:u8(0:u8)
dsa_mem_ffaf0851_1_7452:u8 = low:u8(0:u8)
dsa_mem_ffaf0848_1_7453:u8 = low:u8(0:u8)
dsa_R_EAX_32_1_7454:u32 = 0xffaf0834:u32
dsa_R_YMM1_1_7455:u256 =
  concat:[extract:255:128:[dsa_R_YMM1_1_7260:u256]][
   pad:u128(dsa_mem_ffaf0853_1_7442:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0852_1_7440:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0851_1_7452:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0850_1_7441:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf084f_1_7439:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf084e_1_7449:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf084d_1_7444:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf084c_1_7447:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf084b_1_7438:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf084a_1_7445:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0849_1_7446:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0848_1_7453:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0847_1_7448:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0846_1_7451:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0845_1_7450:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0844_1_7443:u8)))))))))))))))]
addr 0xdcff67bc @asm "movdqu xmm2,XMMWORD PTR [eax+0x20]" @tid "0"
  @context "R_YMM2" = 0x41414141414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf0834, 0, u32, rd
  @context "mem32[0xffaf0854]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0855]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0856]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0857]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0858]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0859]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf085a]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf085b]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf085c]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf085d]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf085e]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf085f]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0860]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0861]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0862]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0863]" = 0x0, 0, u8, rd
label pc_0xdcff67bc
dsa_mem_ffaf085c_1_7456:u8 = low:u8(0:u8)
dsa_mem_ffaf0858_1_7457:u8 = low:u8(0:u8)
dsa_mem_ffaf0855_1_7458:u8 = low:u8(0:u8)
dsa_mem_ffaf0857_1_7459:u8 = low:u8(0:u8)
dsa_mem_ffaf085d_1_7460:u8 = low:u8(0:u8)
dsa_mem_ffaf085e_1_7461:u8 = low:u8(0:u8)
dsa_mem_ffaf0863_1_7462:u8 = low:u8(0:u8)
dsa_mem_ffaf085b_1_7463:u8 = low:u8(0:u8)
dsa_mem_ffaf0860_1_7464:u8 = low:u8(0:u8)
dsa_mem_ffaf0856_1_7465:u8 = low:u8(0:u8)
dsa_mem_ffaf0862_1_7466:u8 = low:u8(0:u8)
dsa_mem_ffaf085f_1_7467:u8 = low:u8(0:u8)
dsa_mem_ffaf0861_1_7468:u8 = low:u8(0:u8)
dsa_mem_ffaf0854_1_7469:u8 = low:u8(0:u8)
dsa_mem_ffaf085a_1_7470:u8 = low:u8(0:u8)
dsa_mem_ffaf0859_1_7471:u8 = low:u8(0:u8)
dsa_R_EAX_32_1_7472:u32 = 0xffaf0834:u32
dsa_R_YMM2_1_7473:u256 =
  concat:[extract:255:128:[dsa_R_YMM2_1_7262:u256]][
   pad:u128(dsa_mem_ffaf0863_1_7462:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0862_1_7466:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0861_1_7468:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0860_1_7464:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf085f_1_7467:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf085e_1_7461:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf085d_1_7460:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf085c_1_7456:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf085b_1_7463:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf085a_1_7470:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0859_1_7471:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0858_1_7457:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0857_1_7459:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0856_1_7465:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0855_1_7458:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0854_1_7469:u8)))))))))))))))]
addr 0xdcff67c1 @asm "movdqu xmm3,XMMWORD PTR [eax+0x30]" @tid "0"
  @context "R_YMM3" = 0xa41414141414141414141414141, -1, u256, wr
  @context "R_EAX_32" = 0xffaf0834, 0, u32, rd
  @context "mem32[0xffaf0864]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0865]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0866]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0867]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0868]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0869]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf086a]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf086b]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf086c]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf086d]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf086e]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf086f]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0870]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0871]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0872]" = 0x0, 0, u8, rd
  @context "mem32[0xffaf0873]" = 0x0, 0, u8, rd
label pc_0xdcff67c1
dsa_mem_ffaf0871_1_7474:u8 = low:u8(0:u8)
dsa_mem_ffaf0867_1_7475:u8 = low:u8(0:u8)
dsa_mem_ffaf0866_1_7476:u8 = low:u8(0:u8)
dsa_mem_ffaf086b_1_7477:u8 = low:u8(0:u8)
dsa_mem_ffaf086f_1_7478:u8 = low:u8(0:u8)
dsa_mem_ffaf0873_1_7479:u8 = low:u8(0:u8)
dsa_mem_ffaf086c_1_7480:u8 = low:u8(0:u8)
dsa_mem_ffaf0869_1_7481:u8 = low:u8(0:u8)
dsa_mem_ffaf086e_1_7482:u8 = low:u8(0:u8)
dsa_mem_ffaf0865_1_7483:u8 = low:u8(0:u8)
dsa_mem_ffaf0872_1_7484:u8 = low:u8(0:u8)
dsa_mem_ffaf0870_1_7485:u8 = low:u8(0:u8)
dsa_mem_ffaf086a_1_7486:u8 = low:u8(0:u8)
dsa_mem_ffaf0868_1_7487:u8 = low:u8(0:u8)
dsa_mem_ffaf0864_1_7488:u8 = low:u8(0:u8)
dsa_mem_ffaf086d_1_7489:u8 = low:u8(0:u8)
dsa_R_EAX_32_1_7490:u32 = 0xffaf0834:u32
dsa_R_YMM3_1_7491:u256 =
  concat:[extract:255:128:[dsa_R_YMM3_1_7266:u256]][
   pad:u128(dsa_mem_ffaf0873_1_7479:u8) << 0x78:u128 |
   (pad:u128(dsa_mem_ffaf0872_1_7484:u8) << 0x70:u128 |
   (pad:u128(dsa_mem_ffaf0871_1_7474:u8) << 0x68:u128 |
   (pad:u128(dsa_mem_ffaf0870_1_7485:u8) << 0x60:u128 |
   (pad:u128(dsa_mem_ffaf086f_1_7478:u8) << 0x58:u128 |
   (pad:u128(dsa_mem_ffaf086e_1_7482:u8) << 0x50:u128 |
   (pad:u128(dsa_mem_ffaf086d_1_7489:u8) << 0x48:u128 |
   (pad:u128(dsa_mem_ffaf086c_1_7480:u8) << 0x40:u128 |
   (pad:u128(dsa_mem_ffaf086b_1_7477:u8) << 0x38:u128 |
   (pad:u128(dsa_mem_ffaf086a_1_7486:u8) << 0x30:u128 |
   (pad:u128(dsa_mem_ffaf0869_1_7481:u8) << 0x28:u128 |
   (pad:u128(dsa_mem_ffaf0868_1_7487:u8) << 0x20:u128 |
   (pad:u128(dsa_mem_ffaf0867_1_7475:u8) << 0x18:u128 |
   (pad:u128(dsa_mem_ffaf0866_1_7476:u8) << 0x10:u128 |
   (pad:u128(dsa_mem_ffaf0865_1_7483:u8) << 8:u128 |
   pad:u128(dsa_mem_ffaf0864_1_7488:u8)))))))))))))))]
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413fa9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7492:bool = false
dsa_T_t_1_7493:u32 = dsa_R_ECX_32_1_7341:u32
dsa_R_ECX_32_1_7494:u32 = dsa_R_ECX_32_1_7341:u32 - 0x80:u32
dsa_R_CF_1_7495:bool = dsa_T_t_1_7493:u32 < 0x80:u32
dsa_R_OF_1_7496:bool =
  high:bool((dsa_T_t_1_7493:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7493:u32 ^ dsa_R_ECX_32_1_7494:u32))
dsa_R_AF_1_7497:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7494:u32 ^ dsa_T_t_1_7493:u32 ^ 0x80:u32))
dsa_R_PF_3_7500:bool =
  ~low:bool(let dsa_T_acc_1_7498:u32 :=
                                         dsa_R_ECX_32_1_7494:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7494:u32 in
            let dsa_T_acc_2_7499:u32 :=
                                         dsa_T_acc_1_7498:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7498:u32 in
            dsa_T_acc_2_7499:u32 >> 1:u32 ^ dsa_T_acc_2_7499:u32)
dsa_R_SF_1_7501:bool = high:bool(dsa_R_ECX_32_1_7494:u32)
dsa_R_ZF_1_7502:bool = 0:u32 == dsa_R_ECX_32_1_7494:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7503:bool = false
dsa_R_EIP_1_7504:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7495:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp171"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413f29, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7505:bool = false
dsa_T_t_1_7506:u32 = dsa_R_ECX_32_1_7494:u32
dsa_R_ECX_32_1_7507:u32 = dsa_R_ECX_32_1_7494:u32 - 0x80:u32
dsa_R_CF_1_7508:bool = dsa_T_t_1_7506:u32 < 0x80:u32
dsa_R_OF_1_7509:bool =
  high:bool((dsa_T_t_1_7506:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7506:u32 ^ dsa_R_ECX_32_1_7507:u32))
dsa_R_AF_1_7510:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7507:u32 ^ dsa_T_t_1_7506:u32 ^ 0x80:u32))
dsa_R_PF_3_7513:bool =
  ~low:bool(let dsa_T_acc_1_7511:u32 :=
                                         dsa_R_ECX_32_1_7507:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7507:u32 in
            let dsa_T_acc_2_7512:u32 :=
                                         dsa_T_acc_1_7511:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7511:u32 in
            dsa_T_acc_2_7512:u32 >> 1:u32 ^ dsa_T_acc_2_7512:u32)
dsa_R_SF_1_7514:bool = high:bool(dsa_R_ECX_32_1_7507:u32)
dsa_R_ZF_1_7515:bool = 0:u32 == dsa_R_ECX_32_1_7507:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7516:bool = false
dsa_R_EIP_1_7517:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7508:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp172"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413ea9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7518:bool = false
dsa_T_t_1_7519:u32 = dsa_R_ECX_32_1_7507:u32
dsa_R_ECX_32_1_7520:u32 = dsa_R_ECX_32_1_7507:u32 - 0x80:u32
dsa_R_CF_1_7521:bool = dsa_T_t_1_7519:u32 < 0x80:u32
dsa_R_OF_1_7522:bool =
  high:bool((dsa_T_t_1_7519:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7519:u32 ^ dsa_R_ECX_32_1_7520:u32))
dsa_R_AF_1_7523:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7520:u32 ^ dsa_T_t_1_7519:u32 ^ 0x80:u32))
dsa_R_PF_3_7526:bool =
  ~low:bool(let dsa_T_acc_1_7524:u32 :=
                                         dsa_R_ECX_32_1_7520:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7520:u32 in
            let dsa_T_acc_2_7525:u32 :=
                                         dsa_T_acc_1_7524:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7524:u32 in
            dsa_T_acc_2_7525:u32 >> 1:u32 ^ dsa_T_acc_2_7525:u32)
dsa_R_SF_1_7527:bool = high:bool(dsa_R_ECX_32_1_7520:u32)
dsa_R_ZF_1_7528:bool = 0:u32 == dsa_R_ECX_32_1_7520:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7529:bool = false
dsa_R_EIP_1_7530:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7521:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp173"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413e29, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7531:bool = false
dsa_T_t_1_7532:u32 = dsa_R_ECX_32_1_7520:u32
dsa_R_ECX_32_1_7533:u32 = dsa_R_ECX_32_1_7520:u32 - 0x80:u32
dsa_R_CF_1_7534:bool = dsa_T_t_1_7532:u32 < 0x80:u32
dsa_R_OF_1_7535:bool =
  high:bool((dsa_T_t_1_7532:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7532:u32 ^ dsa_R_ECX_32_1_7533:u32))
dsa_R_AF_1_7536:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7533:u32 ^ dsa_T_t_1_7532:u32 ^ 0x80:u32))
dsa_R_PF_3_7539:bool =
  ~low:bool(let dsa_T_acc_1_7537:u32 :=
                                         dsa_R_ECX_32_1_7533:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7533:u32 in
            let dsa_T_acc_2_7538:u32 :=
                                         dsa_T_acc_1_7537:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7537:u32 in
            dsa_T_acc_2_7538:u32 >> 1:u32 ^ dsa_T_acc_2_7538:u32)
dsa_R_SF_1_7540:bool = high:bool(dsa_R_ECX_32_1_7533:u32)
dsa_R_ZF_1_7541:bool = 0:u32 == dsa_R_ECX_32_1_7533:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7542:bool = false
dsa_R_EIP_1_7543:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7534:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp174"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413da9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7544:bool = false
dsa_T_t_1_7545:u32 = dsa_R_ECX_32_1_7533:u32
dsa_R_ECX_32_1_7546:u32 = dsa_R_ECX_32_1_7533:u32 - 0x80:u32
dsa_R_CF_1_7547:bool = dsa_T_t_1_7545:u32 < 0x80:u32
dsa_R_OF_1_7548:bool =
  high:bool((dsa_T_t_1_7545:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7545:u32 ^ dsa_R_ECX_32_1_7546:u32))
dsa_R_AF_1_7549:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7546:u32 ^ dsa_T_t_1_7545:u32 ^ 0x80:u32))
dsa_R_PF_3_7552:bool =
  ~low:bool(let dsa_T_acc_1_7550:u32 :=
                                         dsa_R_ECX_32_1_7546:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7546:u32 in
            let dsa_T_acc_2_7551:u32 :=
                                         dsa_T_acc_1_7550:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7550:u32 in
            dsa_T_acc_2_7551:u32 >> 1:u32 ^ dsa_T_acc_2_7551:u32)
dsa_R_SF_1_7553:bool = high:bool(dsa_R_ECX_32_1_7546:u32)
dsa_R_ZF_1_7554:bool = 0:u32 == dsa_R_ECX_32_1_7546:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7555:bool = false
dsa_R_EIP_1_7556:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7547:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp175"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413d29, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7557:bool = false
dsa_T_t_1_7558:u32 = dsa_R_ECX_32_1_7546:u32
dsa_R_ECX_32_1_7559:u32 = dsa_R_ECX_32_1_7546:u32 - 0x80:u32
dsa_R_CF_1_7560:bool = dsa_T_t_1_7558:u32 < 0x80:u32
dsa_R_OF_1_7561:bool =
  high:bool((dsa_T_t_1_7558:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7558:u32 ^ dsa_R_ECX_32_1_7559:u32))
dsa_R_AF_1_7562:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7559:u32 ^ dsa_T_t_1_7558:u32 ^ 0x80:u32))
dsa_R_PF_3_7565:bool =
  ~low:bool(let dsa_T_acc_1_7563:u32 :=
                                         dsa_R_ECX_32_1_7559:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7559:u32 in
            let dsa_T_acc_2_7564:u32 :=
                                         dsa_T_acc_1_7563:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7563:u32 in
            dsa_T_acc_2_7564:u32 >> 1:u32 ^ dsa_T_acc_2_7564:u32)
dsa_R_SF_1_7566:bool = high:bool(dsa_R_ECX_32_1_7559:u32)
dsa_R_ZF_1_7567:bool = 0:u32 == dsa_R_ECX_32_1_7559:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7568:bool = false
dsa_R_EIP_1_7569:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7560:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp176"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413ca9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7570:bool = false
dsa_T_t_1_7571:u32 = dsa_R_ECX_32_1_7559:u32
dsa_R_ECX_32_1_7572:u32 = dsa_R_ECX_32_1_7559:u32 - 0x80:u32
dsa_R_CF_1_7573:bool = dsa_T_t_1_7571:u32 < 0x80:u32
dsa_R_OF_1_7574:bool =
  high:bool((dsa_T_t_1_7571:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7571:u32 ^ dsa_R_ECX_32_1_7572:u32))
dsa_R_AF_1_7575:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7572:u32 ^ dsa_T_t_1_7571:u32 ^ 0x80:u32))
dsa_R_PF_3_7578:bool =
  ~low:bool(let dsa_T_acc_1_7576:u32 :=
                                         dsa_R_ECX_32_1_7572:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7572:u32 in
            let dsa_T_acc_2_7577:u32 :=
                                         dsa_T_acc_1_7576:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7576:u32 in
            dsa_T_acc_2_7577:u32 >> 1:u32 ^ dsa_T_acc_2_7577:u32)
dsa_R_SF_1_7579:bool = high:bool(dsa_R_ECX_32_1_7572:u32)
dsa_R_ZF_1_7580:bool = 0:u32 == dsa_R_ECX_32_1_7572:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7581:bool = false
dsa_R_EIP_1_7582:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7573:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp177"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413c29, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7583:bool = false
dsa_T_t_1_7584:u32 = dsa_R_ECX_32_1_7572:u32
dsa_R_ECX_32_1_7585:u32 = dsa_R_ECX_32_1_7572:u32 - 0x80:u32
dsa_R_CF_1_7586:bool = dsa_T_t_1_7584:u32 < 0x80:u32
dsa_R_OF_1_7587:bool =
  high:bool((dsa_T_t_1_7584:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7584:u32 ^ dsa_R_ECX_32_1_7585:u32))
dsa_R_AF_1_7588:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7585:u32 ^ dsa_T_t_1_7584:u32 ^ 0x80:u32))
dsa_R_PF_3_7591:bool =
  ~low:bool(let dsa_T_acc_1_7589:u32 :=
                                         dsa_R_ECX_32_1_7585:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7585:u32 in
            let dsa_T_acc_2_7590:u32 :=
                                         dsa_T_acc_1_7589:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7589:u32 in
            dsa_T_acc_2_7590:u32 >> 1:u32 ^ dsa_T_acc_2_7590:u32)
dsa_R_SF_1_7592:bool = high:bool(dsa_R_ECX_32_1_7585:u32)
dsa_R_ZF_1_7593:bool = 0:u32 == dsa_R_ECX_32_1_7585:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7594:bool = false
dsa_R_EIP_1_7595:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7586:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp178"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413ba9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7596:bool = false
dsa_T_t_1_7597:u32 = dsa_R_ECX_32_1_7585:u32
dsa_R_ECX_32_1_7598:u32 = dsa_R_ECX_32_1_7585:u32 - 0x80:u32
dsa_R_CF_1_7599:bool = dsa_T_t_1_7597:u32 < 0x80:u32
dsa_R_OF_1_7600:bool =
  high:bool((dsa_T_t_1_7597:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7597:u32 ^ dsa_R_ECX_32_1_7598:u32))
dsa_R_AF_1_7601:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7598:u32 ^ dsa_T_t_1_7597:u32 ^ 0x80:u32))
dsa_R_PF_3_7604:bool =
  ~low:bool(let dsa_T_acc_1_7602:u32 :=
                                         dsa_R_ECX_32_1_7598:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7598:u32 in
            let dsa_T_acc_2_7603:u32 :=
                                         dsa_T_acc_1_7602:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7602:u32 in
            dsa_T_acc_2_7603:u32 >> 1:u32 ^ dsa_T_acc_2_7603:u32)
dsa_R_SF_1_7605:bool = high:bool(dsa_R_ECX_32_1_7598:u32)
dsa_R_ZF_1_7606:bool = 0:u32 == dsa_R_ECX_32_1_7598:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7607:bool = false
dsa_R_EIP_1_7608:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7599:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp179"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413b29, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7609:bool = false
dsa_T_t_1_7610:u32 = dsa_R_ECX_32_1_7598:u32
dsa_R_ECX_32_1_7611:u32 = dsa_R_ECX_32_1_7598:u32 - 0x80:u32
dsa_R_CF_1_7612:bool = dsa_T_t_1_7610:u32 < 0x80:u32
dsa_R_OF_1_7613:bool =
  high:bool((dsa_T_t_1_7610:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7610:u32 ^ dsa_R_ECX_32_1_7611:u32))
dsa_R_AF_1_7614:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7611:u32 ^ dsa_T_t_1_7610:u32 ^ 0x80:u32))
dsa_R_PF_3_7617:bool =
  ~low:bool(let dsa_T_acc_1_7615:u32 :=
                                         dsa_R_ECX_32_1_7611:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7611:u32 in
            let dsa_T_acc_2_7616:u32 :=
                                         dsa_T_acc_1_7615:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7615:u32 in
            dsa_T_acc_2_7616:u32 >> 1:u32 ^ dsa_T_acc_2_7616:u32)
dsa_R_SF_1_7618:bool = high:bool(dsa_R_ECX_32_1_7611:u32)
dsa_R_ZF_1_7619:bool = 0:u32 == dsa_R_ECX_32_1_7611:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7620:bool = false
dsa_R_EIP_1_7621:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7612:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp180"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413aa9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7622:bool = false
dsa_T_t_1_7623:u32 = dsa_R_ECX_32_1_7611:u32
dsa_R_ECX_32_1_7624:u32 = dsa_R_ECX_32_1_7611:u32 - 0x80:u32
dsa_R_CF_1_7625:bool = dsa_T_t_1_7623:u32 < 0x80:u32
dsa_R_OF_1_7626:bool =
  high:bool((dsa_T_t_1_7623:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7623:u32 ^ dsa_R_ECX_32_1_7624:u32))
dsa_R_AF_1_7627:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7624:u32 ^ dsa_T_t_1_7623:u32 ^ 0x80:u32))
dsa_R_PF_3_7630:bool =
  ~low:bool(let dsa_T_acc_1_7628:u32 :=
                                         dsa_R_ECX_32_1_7624:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7624:u32 in
            let dsa_T_acc_2_7629:u32 :=
                                         dsa_T_acc_1_7628:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7628:u32 in
            dsa_T_acc_2_7629:u32 >> 1:u32 ^ dsa_T_acc_2_7629:u32)
dsa_R_SF_1_7631:bool = high:bool(dsa_R_ECX_32_1_7624:u32)
dsa_R_ZF_1_7632:bool = 0:u32 == dsa_R_ECX_32_1_7624:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7633:bool = false
dsa_R_EIP_1_7634:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7625:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp181"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413a29, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7635:bool = false
dsa_T_t_1_7636:u32 = dsa_R_ECX_32_1_7624:u32
dsa_R_ECX_32_1_7637:u32 = dsa_R_ECX_32_1_7624:u32 - 0x80:u32
dsa_R_CF_1_7638:bool = dsa_T_t_1_7636:u32 < 0x80:u32
dsa_R_OF_1_7639:bool =
  high:bool((dsa_T_t_1_7636:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7636:u32 ^ dsa_R_ECX_32_1_7637:u32))
dsa_R_AF_1_7640:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7637:u32 ^ dsa_T_t_1_7636:u32 ^ 0x80:u32))
dsa_R_PF_3_7643:bool =
  ~low:bool(let dsa_T_acc_1_7641:u32 :=
                                         dsa_R_ECX_32_1_7637:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7637:u32 in
            let dsa_T_acc_2_7642:u32 :=
                                         dsa_T_acc_1_7641:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7641:u32 in
            dsa_T_acc_2_7642:u32 >> 1:u32 ^ dsa_T_acc_2_7642:u32)
dsa_R_SF_1_7644:bool = high:bool(dsa_R_ECX_32_1_7637:u32)
dsa_R_ZF_1_7645:bool = 0:u32 == dsa_R_ECX_32_1_7637:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7646:bool = false
dsa_R_EIP_1_7647:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7638:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp182"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414139a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7648:bool = false
dsa_T_t_1_7649:u32 = dsa_R_ECX_32_1_7637:u32
dsa_R_ECX_32_1_7650:u32 = dsa_R_ECX_32_1_7637:u32 - 0x80:u32
dsa_R_CF_1_7651:bool = dsa_T_t_1_7649:u32 < 0x80:u32
dsa_R_OF_1_7652:bool =
  high:bool((dsa_T_t_1_7649:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7649:u32 ^ dsa_R_ECX_32_1_7650:u32))
dsa_R_AF_1_7653:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7650:u32 ^ dsa_T_t_1_7649:u32 ^ 0x80:u32))
dsa_R_PF_3_7656:bool =
  ~low:bool(let dsa_T_acc_1_7654:u32 :=
                                         dsa_R_ECX_32_1_7650:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7650:u32 in
            let dsa_T_acc_2_7655:u32 :=
                                         dsa_T_acc_1_7654:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7654:u32 in
            dsa_T_acc_2_7655:u32 >> 1:u32 ^ dsa_T_acc_2_7655:u32)
dsa_R_SF_1_7657:bool = high:bool(dsa_R_ECX_32_1_7650:u32)
dsa_R_ZF_1_7658:bool = 0:u32 == dsa_R_ECX_32_1_7650:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7659:bool = false
dsa_R_EIP_1_7660:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7651:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp183"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413929, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7661:bool = false
dsa_T_t_1_7662:u32 = dsa_R_ECX_32_1_7650:u32
dsa_R_ECX_32_1_7663:u32 = dsa_R_ECX_32_1_7650:u32 - 0x80:u32
dsa_R_CF_1_7664:bool = dsa_T_t_1_7662:u32 < 0x80:u32
dsa_R_OF_1_7665:bool =
  high:bool((dsa_T_t_1_7662:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7662:u32 ^ dsa_R_ECX_32_1_7663:u32))
dsa_R_AF_1_7666:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7663:u32 ^ dsa_T_t_1_7662:u32 ^ 0x80:u32))
dsa_R_PF_3_7669:bool =
  ~low:bool(let dsa_T_acc_1_7667:u32 :=
                                         dsa_R_ECX_32_1_7663:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7663:u32 in
            let dsa_T_acc_2_7668:u32 :=
                                         dsa_T_acc_1_7667:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7667:u32 in
            dsa_T_acc_2_7668:u32 >> 1:u32 ^ dsa_T_acc_2_7668:u32)
dsa_R_SF_1_7670:bool = high:bool(dsa_R_ECX_32_1_7663:u32)
dsa_R_ZF_1_7671:bool = 0:u32 == dsa_R_ECX_32_1_7663:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7672:bool = false
dsa_R_EIP_1_7673:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7664:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp184"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414138a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7674:bool = false
dsa_T_t_1_7675:u32 = dsa_R_ECX_32_1_7663:u32
dsa_R_ECX_32_1_7676:u32 = dsa_R_ECX_32_1_7663:u32 - 0x80:u32
dsa_R_CF_1_7677:bool = dsa_T_t_1_7675:u32 < 0x80:u32
dsa_R_OF_1_7678:bool =
  high:bool((dsa_T_t_1_7675:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7675:u32 ^ dsa_R_ECX_32_1_7676:u32))
dsa_R_AF_1_7679:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7676:u32 ^ dsa_T_t_1_7675:u32 ^ 0x80:u32))
dsa_R_PF_3_7682:bool =
  ~low:bool(let dsa_T_acc_1_7680:u32 :=
                                         dsa_R_ECX_32_1_7676:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7676:u32 in
            let dsa_T_acc_2_7681:u32 :=
                                         dsa_T_acc_1_7680:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7680:u32 in
            dsa_T_acc_2_7681:u32 >> 1:u32 ^ dsa_T_acc_2_7681:u32)
dsa_R_SF_1_7683:bool = high:bool(dsa_R_ECX_32_1_7676:u32)
dsa_R_ZF_1_7684:bool = 0:u32 == dsa_R_ECX_32_1_7676:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7685:bool = false
dsa_R_EIP_1_7686:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7677:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp185"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413829, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7687:bool = false
dsa_T_t_1_7688:u32 = dsa_R_ECX_32_1_7676:u32
dsa_R_ECX_32_1_7689:u32 = dsa_R_ECX_32_1_7676:u32 - 0x80:u32
dsa_R_CF_1_7690:bool = dsa_T_t_1_7688:u32 < 0x80:u32
dsa_R_OF_1_7691:bool =
  high:bool((dsa_T_t_1_7688:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7688:u32 ^ dsa_R_ECX_32_1_7689:u32))
dsa_R_AF_1_7692:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7689:u32 ^ dsa_T_t_1_7688:u32 ^ 0x80:u32))
dsa_R_PF_3_7695:bool =
  ~low:bool(let dsa_T_acc_1_7693:u32 :=
                                         dsa_R_ECX_32_1_7689:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7689:u32 in
            let dsa_T_acc_2_7694:u32 :=
                                         dsa_T_acc_1_7693:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7693:u32 in
            dsa_T_acc_2_7694:u32 >> 1:u32 ^ dsa_T_acc_2_7694:u32)
dsa_R_SF_1_7696:bool = high:bool(dsa_R_ECX_32_1_7689:u32)
dsa_R_ZF_1_7697:bool = 0:u32 == dsa_R_ECX_32_1_7689:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7698:bool = false
dsa_R_EIP_1_7699:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7690:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp186"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414137a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7700:bool = false
dsa_T_t_1_7701:u32 = dsa_R_ECX_32_1_7689:u32
dsa_R_ECX_32_1_7702:u32 = dsa_R_ECX_32_1_7689:u32 - 0x80:u32
dsa_R_CF_1_7703:bool = dsa_T_t_1_7701:u32 < 0x80:u32
dsa_R_OF_1_7704:bool =
  high:bool((dsa_T_t_1_7701:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7701:u32 ^ dsa_R_ECX_32_1_7702:u32))
dsa_R_AF_1_7705:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7702:u32 ^ dsa_T_t_1_7701:u32 ^ 0x80:u32))
dsa_R_PF_3_7708:bool =
  ~low:bool(let dsa_T_acc_1_7706:u32 :=
                                         dsa_R_ECX_32_1_7702:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7702:u32 in
            let dsa_T_acc_2_7707:u32 :=
                                         dsa_T_acc_1_7706:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7706:u32 in
            dsa_T_acc_2_7707:u32 >> 1:u32 ^ dsa_T_acc_2_7707:u32)
dsa_R_SF_1_7709:bool = high:bool(dsa_R_ECX_32_1_7702:u32)
dsa_R_ZF_1_7710:bool = 0:u32 == dsa_R_ECX_32_1_7702:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7711:bool = false
dsa_R_EIP_1_7712:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7703:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp187"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413729, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7713:bool = false
dsa_T_t_1_7714:u32 = dsa_R_ECX_32_1_7702:u32
dsa_R_ECX_32_1_7715:u32 = dsa_R_ECX_32_1_7702:u32 - 0x80:u32
dsa_R_CF_1_7716:bool = dsa_T_t_1_7714:u32 < 0x80:u32
dsa_R_OF_1_7717:bool =
  high:bool((dsa_T_t_1_7714:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7714:u32 ^ dsa_R_ECX_32_1_7715:u32))
dsa_R_AF_1_7718:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7715:u32 ^ dsa_T_t_1_7714:u32 ^ 0x80:u32))
dsa_R_PF_3_7721:bool =
  ~low:bool(let dsa_T_acc_1_7719:u32 :=
                                         dsa_R_ECX_32_1_7715:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7715:u32 in
            let dsa_T_acc_2_7720:u32 :=
                                         dsa_T_acc_1_7719:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7719:u32 in
            dsa_T_acc_2_7720:u32 >> 1:u32 ^ dsa_T_acc_2_7720:u32)
dsa_R_SF_1_7722:bool = high:bool(dsa_R_ECX_32_1_7715:u32)
dsa_R_ZF_1_7723:bool = 0:u32 == dsa_R_ECX_32_1_7715:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7724:bool = false
dsa_R_EIP_1_7725:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7716:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp188"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414136a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7726:bool = false
dsa_T_t_1_7727:u32 = dsa_R_ECX_32_1_7715:u32
dsa_R_ECX_32_1_7728:u32 = dsa_R_ECX_32_1_7715:u32 - 0x80:u32
dsa_R_CF_1_7729:bool = dsa_T_t_1_7727:u32 < 0x80:u32
dsa_R_OF_1_7730:bool =
  high:bool((dsa_T_t_1_7727:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7727:u32 ^ dsa_R_ECX_32_1_7728:u32))
dsa_R_AF_1_7731:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7728:u32 ^ dsa_T_t_1_7727:u32 ^ 0x80:u32))
dsa_R_PF_3_7734:bool =
  ~low:bool(let dsa_T_acc_1_7732:u32 :=
                                         dsa_R_ECX_32_1_7728:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7728:u32 in
            let dsa_T_acc_2_7733:u32 :=
                                         dsa_T_acc_1_7732:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7732:u32 in
            dsa_T_acc_2_7733:u32 >> 1:u32 ^ dsa_T_acc_2_7733:u32)
dsa_R_SF_1_7735:bool = high:bool(dsa_R_ECX_32_1_7728:u32)
dsa_R_ZF_1_7736:bool = 0:u32 == dsa_R_ECX_32_1_7728:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7737:bool = false
dsa_R_EIP_1_7738:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7729:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp189"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413629, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7739:bool = false
dsa_T_t_1_7740:u32 = dsa_R_ECX_32_1_7728:u32
dsa_R_ECX_32_1_7741:u32 = dsa_R_ECX_32_1_7728:u32 - 0x80:u32
dsa_R_CF_1_7742:bool = dsa_T_t_1_7740:u32 < 0x80:u32
dsa_R_OF_1_7743:bool =
  high:bool((dsa_T_t_1_7740:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7740:u32 ^ dsa_R_ECX_32_1_7741:u32))
dsa_R_AF_1_7744:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7741:u32 ^ dsa_T_t_1_7740:u32 ^ 0x80:u32))
dsa_R_PF_3_7747:bool =
  ~low:bool(let dsa_T_acc_1_7745:u32 :=
                                         dsa_R_ECX_32_1_7741:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7741:u32 in
            let dsa_T_acc_2_7746:u32 :=
                                         dsa_T_acc_1_7745:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7745:u32 in
            dsa_T_acc_2_7746:u32 >> 1:u32 ^ dsa_T_acc_2_7746:u32)
dsa_R_SF_1_7748:bool = high:bool(dsa_R_ECX_32_1_7741:u32)
dsa_R_ZF_1_7749:bool = 0:u32 == dsa_R_ECX_32_1_7741:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7750:bool = false
dsa_R_EIP_1_7751:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7742:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp190"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414135a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7752:bool = false
dsa_T_t_1_7753:u32 = dsa_R_ECX_32_1_7741:u32
dsa_R_ECX_32_1_7754:u32 = dsa_R_ECX_32_1_7741:u32 - 0x80:u32
dsa_R_CF_1_7755:bool = dsa_T_t_1_7753:u32 < 0x80:u32
dsa_R_OF_1_7756:bool =
  high:bool((dsa_T_t_1_7753:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7753:u32 ^ dsa_R_ECX_32_1_7754:u32))
dsa_R_AF_1_7757:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7754:u32 ^ dsa_T_t_1_7753:u32 ^ 0x80:u32))
dsa_R_PF_3_7760:bool =
  ~low:bool(let dsa_T_acc_1_7758:u32 :=
                                         dsa_R_ECX_32_1_7754:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7754:u32 in
            let dsa_T_acc_2_7759:u32 :=
                                         dsa_T_acc_1_7758:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7758:u32 in
            dsa_T_acc_2_7759:u32 >> 1:u32 ^ dsa_T_acc_2_7759:u32)
dsa_R_SF_1_7761:bool = high:bool(dsa_R_ECX_32_1_7754:u32)
dsa_R_ZF_1_7762:bool = 0:u32 == dsa_R_ECX_32_1_7754:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7763:bool = false
dsa_R_EIP_1_7764:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7755:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp191"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413529, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7765:bool = false
dsa_T_t_1_7766:u32 = dsa_R_ECX_32_1_7754:u32
dsa_R_ECX_32_1_7767:u32 = dsa_R_ECX_32_1_7754:u32 - 0x80:u32
dsa_R_CF_1_7768:bool = dsa_T_t_1_7766:u32 < 0x80:u32
dsa_R_OF_1_7769:bool =
  high:bool((dsa_T_t_1_7766:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7766:u32 ^ dsa_R_ECX_32_1_7767:u32))
dsa_R_AF_1_7770:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7767:u32 ^ dsa_T_t_1_7766:u32 ^ 0x80:u32))
dsa_R_PF_3_7773:bool =
  ~low:bool(let dsa_T_acc_1_7771:u32 :=
                                         dsa_R_ECX_32_1_7767:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7767:u32 in
            let dsa_T_acc_2_7772:u32 :=
                                         dsa_T_acc_1_7771:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7771:u32 in
            dsa_T_acc_2_7772:u32 >> 1:u32 ^ dsa_T_acc_2_7772:u32)
dsa_R_SF_1_7774:bool = high:bool(dsa_R_ECX_32_1_7767:u32)
dsa_R_ZF_1_7775:bool = 0:u32 == dsa_R_ECX_32_1_7767:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7776:bool = false
dsa_R_EIP_1_7777:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7768:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp192"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414134a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7778:bool = false
dsa_T_t_1_7779:u32 = dsa_R_ECX_32_1_7767:u32
dsa_R_ECX_32_1_7780:u32 = dsa_R_ECX_32_1_7767:u32 - 0x80:u32
dsa_R_CF_1_7781:bool = dsa_T_t_1_7779:u32 < 0x80:u32
dsa_R_OF_1_7782:bool =
  high:bool((dsa_T_t_1_7779:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7779:u32 ^ dsa_R_ECX_32_1_7780:u32))
dsa_R_AF_1_7783:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7780:u32 ^ dsa_T_t_1_7779:u32 ^ 0x80:u32))
dsa_R_PF_3_7786:bool =
  ~low:bool(let dsa_T_acc_1_7784:u32 :=
                                         dsa_R_ECX_32_1_7780:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7780:u32 in
            let dsa_T_acc_2_7785:u32 :=
                                         dsa_T_acc_1_7784:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7784:u32 in
            dsa_T_acc_2_7785:u32 >> 1:u32 ^ dsa_T_acc_2_7785:u32)
dsa_R_SF_1_7787:bool = high:bool(dsa_R_ECX_32_1_7780:u32)
dsa_R_ZF_1_7788:bool = 0:u32 == dsa_R_ECX_32_1_7780:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7789:bool = false
dsa_R_EIP_1_7790:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7781:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp193"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413429, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7791:bool = false
dsa_T_t_1_7792:u32 = dsa_R_ECX_32_1_7780:u32
dsa_R_ECX_32_1_7793:u32 = dsa_R_ECX_32_1_7780:u32 - 0x80:u32
dsa_R_CF_1_7794:bool = dsa_T_t_1_7792:u32 < 0x80:u32
dsa_R_OF_1_7795:bool =
  high:bool((dsa_T_t_1_7792:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7792:u32 ^ dsa_R_ECX_32_1_7793:u32))
dsa_R_AF_1_7796:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7793:u32 ^ dsa_T_t_1_7792:u32 ^ 0x80:u32))
dsa_R_PF_3_7799:bool =
  ~low:bool(let dsa_T_acc_1_7797:u32 :=
                                         dsa_R_ECX_32_1_7793:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7793:u32 in
            let dsa_T_acc_2_7798:u32 :=
                                         dsa_T_acc_1_7797:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7797:u32 in
            dsa_T_acc_2_7798:u32 >> 1:u32 ^ dsa_T_acc_2_7798:u32)
dsa_R_SF_1_7800:bool = high:bool(dsa_R_ECX_32_1_7793:u32)
dsa_R_ZF_1_7801:bool = 0:u32 == dsa_R_ECX_32_1_7793:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7802:bool = false
dsa_R_EIP_1_7803:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7794:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp194"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414133a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7804:bool = false
dsa_T_t_1_7805:u32 = dsa_R_ECX_32_1_7793:u32
dsa_R_ECX_32_1_7806:u32 = dsa_R_ECX_32_1_7793:u32 - 0x80:u32
dsa_R_CF_1_7807:bool = dsa_T_t_1_7805:u32 < 0x80:u32
dsa_R_OF_1_7808:bool =
  high:bool((dsa_T_t_1_7805:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7805:u32 ^ dsa_R_ECX_32_1_7806:u32))
dsa_R_AF_1_7809:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7806:u32 ^ dsa_T_t_1_7805:u32 ^ 0x80:u32))
dsa_R_PF_3_7812:bool =
  ~low:bool(let dsa_T_acc_1_7810:u32 :=
                                         dsa_R_ECX_32_1_7806:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7806:u32 in
            let dsa_T_acc_2_7811:u32 :=
                                         dsa_T_acc_1_7810:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7810:u32 in
            dsa_T_acc_2_7811:u32 >> 1:u32 ^ dsa_T_acc_2_7811:u32)
dsa_R_SF_1_7813:bool = high:bool(dsa_R_ECX_32_1_7806:u32)
dsa_R_ZF_1_7814:bool = 0:u32 == dsa_R_ECX_32_1_7806:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7815:bool = false
dsa_R_EIP_1_7816:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7807:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp195"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413329, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7817:bool = false
dsa_T_t_1_7818:u32 = dsa_R_ECX_32_1_7806:u32
dsa_R_ECX_32_1_7819:u32 = dsa_R_ECX_32_1_7806:u32 - 0x80:u32
dsa_R_CF_1_7820:bool = dsa_T_t_1_7818:u32 < 0x80:u32
dsa_R_OF_1_7821:bool =
  high:bool((dsa_T_t_1_7818:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7818:u32 ^ dsa_R_ECX_32_1_7819:u32))
dsa_R_AF_1_7822:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7819:u32 ^ dsa_T_t_1_7818:u32 ^ 0x80:u32))
dsa_R_PF_3_7825:bool =
  ~low:bool(let dsa_T_acc_1_7823:u32 :=
                                         dsa_R_ECX_32_1_7819:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7819:u32 in
            let dsa_T_acc_2_7824:u32 :=
                                         dsa_T_acc_1_7823:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7823:u32 in
            dsa_T_acc_2_7824:u32 >> 1:u32 ^ dsa_T_acc_2_7824:u32)
dsa_R_SF_1_7826:bool = high:bool(dsa_R_ECX_32_1_7819:u32)
dsa_R_ZF_1_7827:bool = 0:u32 == dsa_R_ECX_32_1_7819:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7828:bool = false
dsa_R_EIP_1_7829:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7820:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp196"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414132a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7830:bool = false
dsa_T_t_1_7831:u32 = dsa_R_ECX_32_1_7819:u32
dsa_R_ECX_32_1_7832:u32 = dsa_R_ECX_32_1_7819:u32 - 0x80:u32
dsa_R_CF_1_7833:bool = dsa_T_t_1_7831:u32 < 0x80:u32
dsa_R_OF_1_7834:bool =
  high:bool((dsa_T_t_1_7831:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7831:u32 ^ dsa_R_ECX_32_1_7832:u32))
dsa_R_AF_1_7835:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7832:u32 ^ dsa_T_t_1_7831:u32 ^ 0x80:u32))
dsa_R_PF_3_7838:bool =
  ~low:bool(let dsa_T_acc_1_7836:u32 :=
                                         dsa_R_ECX_32_1_7832:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7832:u32 in
            let dsa_T_acc_2_7837:u32 :=
                                         dsa_T_acc_1_7836:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7836:u32 in
            dsa_T_acc_2_7837:u32 >> 1:u32 ^ dsa_T_acc_2_7837:u32)
dsa_R_SF_1_7839:bool = high:bool(dsa_R_ECX_32_1_7832:u32)
dsa_R_ZF_1_7840:bool = 0:u32 == dsa_R_ECX_32_1_7832:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7841:bool = false
dsa_R_EIP_1_7842:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7833:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp197"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413229, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7843:bool = false
dsa_T_t_1_7844:u32 = dsa_R_ECX_32_1_7832:u32
dsa_R_ECX_32_1_7845:u32 = dsa_R_ECX_32_1_7832:u32 - 0x80:u32
dsa_R_CF_1_7846:bool = dsa_T_t_1_7844:u32 < 0x80:u32
dsa_R_OF_1_7847:bool =
  high:bool((dsa_T_t_1_7844:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7844:u32 ^ dsa_R_ECX_32_1_7845:u32))
dsa_R_AF_1_7848:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7845:u32 ^ dsa_T_t_1_7844:u32 ^ 0x80:u32))
dsa_R_PF_3_7851:bool =
  ~low:bool(let dsa_T_acc_1_7849:u32 :=
                                         dsa_R_ECX_32_1_7845:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7845:u32 in
            let dsa_T_acc_2_7850:u32 :=
                                         dsa_T_acc_1_7849:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7849:u32 in
            dsa_T_acc_2_7850:u32 >> 1:u32 ^ dsa_T_acc_2_7850:u32)
dsa_R_SF_1_7852:bool = high:bool(dsa_R_ECX_32_1_7845:u32)
dsa_R_ZF_1_7853:bool = 0:u32 == dsa_R_ECX_32_1_7845:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7854:bool = false
dsa_R_EIP_1_7855:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7846:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp198"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414131a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7856:bool = false
dsa_T_t_1_7857:u32 = dsa_R_ECX_32_1_7845:u32
dsa_R_ECX_32_1_7858:u32 = dsa_R_ECX_32_1_7845:u32 - 0x80:u32
dsa_R_CF_1_7859:bool = dsa_T_t_1_7857:u32 < 0x80:u32
dsa_R_OF_1_7860:bool =
  high:bool((dsa_T_t_1_7857:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7857:u32 ^ dsa_R_ECX_32_1_7858:u32))
dsa_R_AF_1_7861:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7858:u32 ^ dsa_T_t_1_7857:u32 ^ 0x80:u32))
dsa_R_PF_3_7864:bool =
  ~low:bool(let dsa_T_acc_1_7862:u32 :=
                                         dsa_R_ECX_32_1_7858:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7858:u32 in
            let dsa_T_acc_2_7863:u32 :=
                                         dsa_T_acc_1_7862:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7862:u32 in
            dsa_T_acc_2_7863:u32 >> 1:u32 ^ dsa_T_acc_2_7863:u32)
dsa_R_SF_1_7865:bool = high:bool(dsa_R_ECX_32_1_7858:u32)
dsa_R_ZF_1_7866:bool = 0:u32 == dsa_R_ECX_32_1_7858:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7867:bool = false
dsa_R_EIP_1_7868:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7859:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp199"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413129, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7869:bool = false
dsa_T_t_1_7870:u32 = dsa_R_ECX_32_1_7858:u32
dsa_R_ECX_32_1_7871:u32 = dsa_R_ECX_32_1_7858:u32 - 0x80:u32
dsa_R_CF_1_7872:bool = dsa_T_t_1_7870:u32 < 0x80:u32
dsa_R_OF_1_7873:bool =
  high:bool((dsa_T_t_1_7870:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7870:u32 ^ dsa_R_ECX_32_1_7871:u32))
dsa_R_AF_1_7874:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7871:u32 ^ dsa_T_t_1_7870:u32 ^ 0x80:u32))
dsa_R_PF_3_7877:bool =
  ~low:bool(let dsa_T_acc_1_7875:u32 :=
                                         dsa_R_ECX_32_1_7871:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7871:u32 in
            let dsa_T_acc_2_7876:u32 :=
                                         dsa_T_acc_1_7875:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7875:u32 in
            dsa_T_acc_2_7876:u32 >> 1:u32 ^ dsa_T_acc_2_7876:u32)
dsa_R_SF_1_7878:bool = high:bool(dsa_R_ECX_32_1_7871:u32)
dsa_R_ZF_1_7879:bool = 0:u32 == dsa_R_ECX_32_1_7871:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7880:bool = false
dsa_R_EIP_1_7881:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7872:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp200"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414130a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7882:bool = false
dsa_T_t_1_7883:u32 = dsa_R_ECX_32_1_7871:u32
dsa_R_ECX_32_1_7884:u32 = dsa_R_ECX_32_1_7871:u32 - 0x80:u32
dsa_R_CF_1_7885:bool = dsa_T_t_1_7883:u32 < 0x80:u32
dsa_R_OF_1_7886:bool =
  high:bool((dsa_T_t_1_7883:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7883:u32 ^ dsa_R_ECX_32_1_7884:u32))
dsa_R_AF_1_7887:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7884:u32 ^ dsa_T_t_1_7883:u32 ^ 0x80:u32))
dsa_R_PF_3_7890:bool =
  ~low:bool(let dsa_T_acc_1_7888:u32 :=
                                         dsa_R_ECX_32_1_7884:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7884:u32 in
            let dsa_T_acc_2_7889:u32 :=
                                         dsa_T_acc_1_7888:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7888:u32 in
            dsa_T_acc_2_7889:u32 >> 1:u32 ^ dsa_T_acc_2_7889:u32)
dsa_R_SF_1_7891:bool = high:bool(dsa_R_ECX_32_1_7884:u32)
dsa_R_ZF_1_7892:bool = 0:u32 == dsa_R_ECX_32_1_7884:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7893:bool = false
dsa_R_EIP_1_7894:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7885:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp201"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41413029, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7895:bool = false
dsa_T_t_1_7896:u32 = dsa_R_ECX_32_1_7884:u32
dsa_R_ECX_32_1_7897:u32 = dsa_R_ECX_32_1_7884:u32 - 0x80:u32
dsa_R_CF_1_7898:bool = dsa_T_t_1_7896:u32 < 0x80:u32
dsa_R_OF_1_7899:bool =
  high:bool((dsa_T_t_1_7896:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7896:u32 ^ dsa_R_ECX_32_1_7897:u32))
dsa_R_AF_1_7900:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7897:u32 ^ dsa_T_t_1_7896:u32 ^ 0x80:u32))
dsa_R_PF_3_7903:bool =
  ~low:bool(let dsa_T_acc_1_7901:u32 :=
                                         dsa_R_ECX_32_1_7897:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7897:u32 in
            let dsa_T_acc_2_7902:u32 :=
                                         dsa_T_acc_1_7901:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7901:u32 in
            dsa_T_acc_2_7902:u32 >> 1:u32 ^ dsa_T_acc_2_7902:u32)
dsa_R_SF_1_7904:bool = high:bool(dsa_R_ECX_32_1_7897:u32)
dsa_R_ZF_1_7905:bool = 0:u32 == dsa_R_ECX_32_1_7897:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7906:bool = false
dsa_R_EIP_1_7907:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7898:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp202"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412fa9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7908:bool = false
dsa_T_t_1_7909:u32 = dsa_R_ECX_32_1_7897:u32
dsa_R_ECX_32_1_7910:u32 = dsa_R_ECX_32_1_7897:u32 - 0x80:u32
dsa_R_CF_1_7911:bool = dsa_T_t_1_7909:u32 < 0x80:u32
dsa_R_OF_1_7912:bool =
  high:bool((dsa_T_t_1_7909:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7909:u32 ^ dsa_R_ECX_32_1_7910:u32))
dsa_R_AF_1_7913:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7910:u32 ^ dsa_T_t_1_7909:u32 ^ 0x80:u32))
dsa_R_PF_3_7916:bool =
  ~low:bool(let dsa_T_acc_1_7914:u32 :=
                                         dsa_R_ECX_32_1_7910:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7910:u32 in
            let dsa_T_acc_2_7915:u32 :=
                                         dsa_T_acc_1_7914:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7914:u32 in
            dsa_T_acc_2_7915:u32 >> 1:u32 ^ dsa_T_acc_2_7915:u32)
dsa_R_SF_1_7917:bool = high:bool(dsa_R_ECX_32_1_7910:u32)
dsa_R_ZF_1_7918:bool = 0:u32 == dsa_R_ECX_32_1_7910:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7919:bool = false
dsa_R_EIP_1_7920:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7911:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp203"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412f29, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7921:bool = false
dsa_T_t_1_7922:u32 = dsa_R_ECX_32_1_7910:u32
dsa_R_ECX_32_1_7923:u32 = dsa_R_ECX_32_1_7910:u32 - 0x80:u32
dsa_R_CF_1_7924:bool = dsa_T_t_1_7922:u32 < 0x80:u32
dsa_R_OF_1_7925:bool =
  high:bool((dsa_T_t_1_7922:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7922:u32 ^ dsa_R_ECX_32_1_7923:u32))
dsa_R_AF_1_7926:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7923:u32 ^ dsa_T_t_1_7922:u32 ^ 0x80:u32))
dsa_R_PF_3_7929:bool =
  ~low:bool(let dsa_T_acc_1_7927:u32 :=
                                         dsa_R_ECX_32_1_7923:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7923:u32 in
            let dsa_T_acc_2_7928:u32 :=
                                         dsa_T_acc_1_7927:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7927:u32 in
            dsa_T_acc_2_7928:u32 >> 1:u32 ^ dsa_T_acc_2_7928:u32)
dsa_R_SF_1_7930:bool = high:bool(dsa_R_ECX_32_1_7923:u32)
dsa_R_ZF_1_7931:bool = 0:u32 == dsa_R_ECX_32_1_7923:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7932:bool = false
dsa_R_EIP_1_7933:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7924:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp204"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412ea9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7934:bool = false
dsa_T_t_1_7935:u32 = dsa_R_ECX_32_1_7923:u32
dsa_R_ECX_32_1_7936:u32 = dsa_R_ECX_32_1_7923:u32 - 0x80:u32
dsa_R_CF_1_7937:bool = dsa_T_t_1_7935:u32 < 0x80:u32
dsa_R_OF_1_7938:bool =
  high:bool((dsa_T_t_1_7935:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7935:u32 ^ dsa_R_ECX_32_1_7936:u32))
dsa_R_AF_1_7939:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7936:u32 ^ dsa_T_t_1_7935:u32 ^ 0x80:u32))
dsa_R_PF_3_7942:bool =
  ~low:bool(let dsa_T_acc_1_7940:u32 :=
                                         dsa_R_ECX_32_1_7936:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7936:u32 in
            let dsa_T_acc_2_7941:u32 :=
                                         dsa_T_acc_1_7940:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7940:u32 in
            dsa_T_acc_2_7941:u32 >> 1:u32 ^ dsa_T_acc_2_7941:u32)
dsa_R_SF_1_7943:bool = high:bool(dsa_R_ECX_32_1_7936:u32)
dsa_R_ZF_1_7944:bool = 0:u32 == dsa_R_ECX_32_1_7936:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7945:bool = false
dsa_R_EIP_1_7946:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7937:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp205"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412e29, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7947:bool = false
dsa_T_t_1_7948:u32 = dsa_R_ECX_32_1_7936:u32
dsa_R_ECX_32_1_7949:u32 = dsa_R_ECX_32_1_7936:u32 - 0x80:u32
dsa_R_CF_1_7950:bool = dsa_T_t_1_7948:u32 < 0x80:u32
dsa_R_OF_1_7951:bool =
  high:bool((dsa_T_t_1_7948:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7948:u32 ^ dsa_R_ECX_32_1_7949:u32))
dsa_R_AF_1_7952:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7949:u32 ^ dsa_T_t_1_7948:u32 ^ 0x80:u32))
dsa_R_PF_3_7955:bool =
  ~low:bool(let dsa_T_acc_1_7953:u32 :=
                                         dsa_R_ECX_32_1_7949:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7949:u32 in
            let dsa_T_acc_2_7954:u32 :=
                                         dsa_T_acc_1_7953:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7953:u32 in
            dsa_T_acc_2_7954:u32 >> 1:u32 ^ dsa_T_acc_2_7954:u32)
dsa_R_SF_1_7956:bool = high:bool(dsa_R_ECX_32_1_7949:u32)
dsa_R_ZF_1_7957:bool = 0:u32 == dsa_R_ECX_32_1_7949:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7958:bool = false
dsa_R_EIP_1_7959:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7950:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp206"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412da9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7960:bool = false
dsa_T_t_1_7961:u32 = dsa_R_ECX_32_1_7949:u32
dsa_R_ECX_32_1_7962:u32 = dsa_R_ECX_32_1_7949:u32 - 0x80:u32
dsa_R_CF_1_7963:bool = dsa_T_t_1_7961:u32 < 0x80:u32
dsa_R_OF_1_7964:bool =
  high:bool((dsa_T_t_1_7961:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7961:u32 ^ dsa_R_ECX_32_1_7962:u32))
dsa_R_AF_1_7965:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7962:u32 ^ dsa_T_t_1_7961:u32 ^ 0x80:u32))
dsa_R_PF_3_7968:bool =
  ~low:bool(let dsa_T_acc_1_7966:u32 :=
                                         dsa_R_ECX_32_1_7962:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7962:u32 in
            let dsa_T_acc_2_7967:u32 :=
                                         dsa_T_acc_1_7966:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7966:u32 in
            dsa_T_acc_2_7967:u32 >> 1:u32 ^ dsa_T_acc_2_7967:u32)
dsa_R_SF_1_7969:bool = high:bool(dsa_R_ECX_32_1_7962:u32)
dsa_R_ZF_1_7970:bool = 0:u32 == dsa_R_ECX_32_1_7962:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7971:bool = false
dsa_R_EIP_1_7972:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7963:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp207"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412d29, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7973:bool = false
dsa_T_t_1_7974:u32 = dsa_R_ECX_32_1_7962:u32
dsa_R_ECX_32_1_7975:u32 = dsa_R_ECX_32_1_7962:u32 - 0x80:u32
dsa_R_CF_1_7976:bool = dsa_T_t_1_7974:u32 < 0x80:u32
dsa_R_OF_1_7977:bool =
  high:bool((dsa_T_t_1_7974:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7974:u32 ^ dsa_R_ECX_32_1_7975:u32))
dsa_R_AF_1_7978:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7975:u32 ^ dsa_T_t_1_7974:u32 ^ 0x80:u32))
dsa_R_PF_3_7981:bool =
  ~low:bool(let dsa_T_acc_1_7979:u32 :=
                                         dsa_R_ECX_32_1_7975:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7975:u32 in
            let dsa_T_acc_2_7980:u32 :=
                                         dsa_T_acc_1_7979:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7979:u32 in
            dsa_T_acc_2_7980:u32 >> 1:u32 ^ dsa_T_acc_2_7980:u32)
dsa_R_SF_1_7982:bool = high:bool(dsa_R_ECX_32_1_7975:u32)
dsa_R_ZF_1_7983:bool = 0:u32 == dsa_R_ECX_32_1_7975:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7984:bool = false
dsa_R_EIP_1_7985:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7976:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp208"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412ca9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7986:bool = false
dsa_T_t_1_7987:u32 = dsa_R_ECX_32_1_7975:u32
dsa_R_ECX_32_1_7988:u32 = dsa_R_ECX_32_1_7975:u32 - 0x80:u32
dsa_R_CF_1_7989:bool = dsa_T_t_1_7987:u32 < 0x80:u32
dsa_R_OF_1_7990:bool =
  high:bool((dsa_T_t_1_7987:u32 ^ 0x80:u32) &
            (dsa_T_t_1_7987:u32 ^ dsa_R_ECX_32_1_7988:u32))
dsa_R_AF_1_7991:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_7988:u32 ^ dsa_T_t_1_7987:u32 ^ 0x80:u32))
dsa_R_PF_3_7994:bool =
  ~low:bool(let dsa_T_acc_1_7992:u32 :=
                                         dsa_R_ECX_32_1_7988:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_7988:u32 in
            let dsa_T_acc_2_7993:u32 :=
                                         dsa_T_acc_1_7992:u32 >> 2:u32 ^
                                         dsa_T_acc_1_7992:u32 in
            dsa_T_acc_2_7993:u32 >> 1:u32 ^ dsa_T_acc_2_7993:u32)
dsa_R_SF_1_7995:bool = high:bool(dsa_R_ECX_32_1_7988:u32)
dsa_R_ZF_1_7996:bool = 0:u32 == dsa_R_ECX_32_1_7988:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_7997:bool = false
dsa_R_EIP_1_7998:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_7989:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp209"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412c29, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_7999:bool = false
dsa_T_t_1_8000:u32 = dsa_R_ECX_32_1_7988:u32
dsa_R_ECX_32_1_8001:u32 = dsa_R_ECX_32_1_7988:u32 - 0x80:u32
dsa_R_CF_1_8002:bool = dsa_T_t_1_8000:u32 < 0x80:u32
dsa_R_OF_1_8003:bool =
  high:bool((dsa_T_t_1_8000:u32 ^ 0x80:u32) &
            (dsa_T_t_1_8000:u32 ^ dsa_R_ECX_32_1_8001:u32))
dsa_R_AF_1_8004:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_8001:u32 ^ dsa_T_t_1_8000:u32 ^ 0x80:u32))
dsa_R_PF_3_8007:bool =
  ~low:bool(let dsa_T_acc_1_8005:u32 :=
                                         dsa_R_ECX_32_1_8001:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_8001:u32 in
            let dsa_T_acc_2_8006:u32 :=
                                         dsa_T_acc_1_8005:u32 >> 2:u32 ^
                                         dsa_T_acc_1_8005:u32 in
            dsa_T_acc_2_8006:u32 >> 1:u32 ^ dsa_T_acc_2_8006:u32)
dsa_R_SF_1_8008:bool = high:bool(dsa_R_ECX_32_1_8001:u32)
dsa_R_ZF_1_8009:bool = 0:u32 == dsa_R_ECX_32_1_8001:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_8010:bool = false
dsa_R_EIP_1_8011:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_8002:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp210"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412ba9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_8012:bool = false
dsa_T_t_1_8013:u32 = dsa_R_ECX_32_1_8001:u32
dsa_R_ECX_32_1_8014:u32 = dsa_R_ECX_32_1_8001:u32 - 0x80:u32
dsa_R_CF_1_8015:bool = dsa_T_t_1_8013:u32 < 0x80:u32
dsa_R_OF_1_8016:bool =
  high:bool((dsa_T_t_1_8013:u32 ^ 0x80:u32) &
            (dsa_T_t_1_8013:u32 ^ dsa_R_ECX_32_1_8014:u32))
dsa_R_AF_1_8017:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_8014:u32 ^ dsa_T_t_1_8013:u32 ^ 0x80:u32))
dsa_R_PF_3_8020:bool =
  ~low:bool(let dsa_T_acc_1_8018:u32 :=
                                         dsa_R_ECX_32_1_8014:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_8014:u32 in
            let dsa_T_acc_2_8019:u32 :=
                                         dsa_T_acc_1_8018:u32 >> 2:u32 ^
                                         dsa_T_acc_1_8018:u32 in
            dsa_T_acc_2_8019:u32 >> 1:u32 ^ dsa_T_acc_2_8019:u32)
dsa_R_SF_1_8021:bool = high:bool(dsa_R_ECX_32_1_8014:u32)
dsa_R_ZF_1_8022:bool = 0:u32 == dsa_R_ECX_32_1_8014:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_8023:bool = false
dsa_R_EIP_1_8024:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_8015:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp211"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412b29, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_8025:bool = false
dsa_T_t_1_8026:u32 = dsa_R_ECX_32_1_8014:u32
dsa_R_ECX_32_1_8027:u32 = dsa_R_ECX_32_1_8014:u32 - 0x80:u32
dsa_R_CF_1_8028:bool = dsa_T_t_1_8026:u32 < 0x80:u32
dsa_R_OF_1_8029:bool =
  high:bool((dsa_T_t_1_8026:u32 ^ 0x80:u32) &
            (dsa_T_t_1_8026:u32 ^ dsa_R_ECX_32_1_8027:u32))
dsa_R_AF_1_8030:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_8027:u32 ^ dsa_T_t_1_8026:u32 ^ 0x80:u32))
dsa_R_PF_3_8033:bool =
  ~low:bool(let dsa_T_acc_1_8031:u32 :=
                                         dsa_R_ECX_32_1_8027:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_8027:u32 in
            let dsa_T_acc_2_8032:u32 :=
                                         dsa_T_acc_1_8031:u32 >> 2:u32 ^
                                         dsa_T_acc_1_8031:u32 in
            dsa_T_acc_2_8032:u32 >> 1:u32 ^ dsa_T_acc_2_8032:u32)
dsa_R_SF_1_8034:bool = high:bool(dsa_R_ECX_32_1_8027:u32)
dsa_R_ZF_1_8035:bool = 0:u32 == dsa_R_ECX_32_1_8027:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_8036:bool = false
dsa_R_EIP_1_8037:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_8028:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp212"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412aa9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_8038:bool = false
dsa_T_t_1_8039:u32 = dsa_R_ECX_32_1_8027:u32
dsa_R_ECX_32_1_8040:u32 = dsa_R_ECX_32_1_8027:u32 - 0x80:u32
dsa_R_CF_1_8041:bool = dsa_T_t_1_8039:u32 < 0x80:u32
dsa_R_OF_1_8042:bool =
  high:bool((dsa_T_t_1_8039:u32 ^ 0x80:u32) &
            (dsa_T_t_1_8039:u32 ^ dsa_R_ECX_32_1_8040:u32))
dsa_R_AF_1_8043:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_8040:u32 ^ dsa_T_t_1_8039:u32 ^ 0x80:u32))
dsa_R_PF_3_8046:bool =
  ~low:bool(let dsa_T_acc_1_8044:u32 :=
                                         dsa_R_ECX_32_1_8040:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_8040:u32 in
            let dsa_T_acc_2_8045:u32 :=
                                         dsa_T_acc_1_8044:u32 >> 2:u32 ^
                                         dsa_T_acc_1_8044:u32 in
            dsa_T_acc_2_8045:u32 >> 1:u32 ^ dsa_T_acc_2_8045:u32)
dsa_R_SF_1_8047:bool = high:bool(dsa_R_ECX_32_1_8040:u32)
dsa_R_ZF_1_8048:bool = 0:u32 == dsa_R_ECX_32_1_8040:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_8049:bool = false
dsa_R_EIP_1_8050:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_8041:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp213"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412a29, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_8051:bool = false
dsa_T_t_1_8052:u32 = dsa_R_ECX_32_1_8040:u32
dsa_R_ECX_32_1_8053:u32 = dsa_R_ECX_32_1_8040:u32 - 0x80:u32
dsa_R_CF_1_8054:bool = dsa_T_t_1_8052:u32 < 0x80:u32
dsa_R_OF_1_8055:bool =
  high:bool((dsa_T_t_1_8052:u32 ^ 0x80:u32) &
            (dsa_T_t_1_8052:u32 ^ dsa_R_ECX_32_1_8053:u32))
dsa_R_AF_1_8056:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_8053:u32 ^ dsa_T_t_1_8052:u32 ^ 0x80:u32))
dsa_R_PF_3_8059:bool =
  ~low:bool(let dsa_T_acc_1_8057:u32 :=
                                         dsa_R_ECX_32_1_8053:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_8053:u32 in
            let dsa_T_acc_2_8058:u32 :=
                                         dsa_T_acc_1_8057:u32 >> 2:u32 ^
                                         dsa_T_acc_1_8057:u32 in
            dsa_T_acc_2_8058:u32 >> 1:u32 ^ dsa_T_acc_2_8058:u32)
dsa_R_SF_1_8060:bool = high:bool(dsa_R_ECX_32_1_8053:u32)
dsa_R_ZF_1_8061:bool = 0:u32 == dsa_R_ECX_32_1_8053:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_8062:bool = false
dsa_R_EIP_1_8063:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_8054:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp214"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414129a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_8064:bool = false
dsa_T_t_1_8065:u32 = dsa_R_ECX_32_1_8053:u32
dsa_R_ECX_32_1_8066:u32 = dsa_R_ECX_32_1_8053:u32 - 0x80:u32
dsa_R_CF_1_8067:bool = dsa_T_t_1_8065:u32 < 0x80:u32
dsa_R_OF_1_8068:bool =
  high:bool((dsa_T_t_1_8065:u32 ^ 0x80:u32) &
            (dsa_T_t_1_8065:u32 ^ dsa_R_ECX_32_1_8066:u32))
dsa_R_AF_1_8069:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_8066:u32 ^ dsa_T_t_1_8065:u32 ^ 0x80:u32))
dsa_R_PF_3_8072:bool =
  ~low:bool(let dsa_T_acc_1_8070:u32 :=
                                         dsa_R_ECX_32_1_8066:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_8066:u32 in
            let dsa_T_acc_2_8071:u32 :=
                                         dsa_T_acc_1_8070:u32 >> 2:u32 ^
                                         dsa_T_acc_1_8070:u32 in
            dsa_T_acc_2_8071:u32 >> 1:u32 ^ dsa_T_acc_2_8071:u32)
dsa_R_SF_1_8073:bool = high:bool(dsa_R_ECX_32_1_8066:u32)
dsa_R_ZF_1_8074:bool = 0:u32 == dsa_R_ECX_32_1_8066:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_8075:bool = false
dsa_R_EIP_1_8076:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_8067:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp215"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x41412929, -1, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_8077:bool = false
dsa_T_t_1_8078:u32 = dsa_R_ECX_32_1_8066:u32
dsa_R_ECX_32_1_8079:u32 = dsa_R_ECX_32_1_8066:u32 - 0x80:u32
dsa_R_CF_1_8080:bool = dsa_T_t_1_8078:u32 < 0x80:u32
dsa_R_OF_1_8081:bool =
  high:bool((dsa_T_t_1_8078:u32 ^ 0x80:u32) &
            (dsa_T_t_1_8078:u32 ^ dsa_R_ECX_32_1_8079:u32))
dsa_R_AF_1_8082:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_8079:u32 ^ dsa_T_t_1_8078:u32 ^ 0x80:u32))
dsa_R_PF_3_8085:bool =
  ~low:bool(let dsa_T_acc_1_8083:u32 :=
                                         dsa_R_ECX_32_1_8079:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_8079:u32 in
            let dsa_T_acc_2_8084:u32 :=
                                         dsa_T_acc_1_8083:u32 >> 2:u32 ^
                                         dsa_T_acc_1_8083:u32 in
            dsa_T_acc_2_8084:u32 >> 1:u32 ^ dsa_T_acc_2_8084:u32)
dsa_R_SF_1_8086:bool = high:bool(dsa_R_ECX_32_1_8079:u32)
dsa_R_ZF_1_8087:bool = 0:u32 == dsa_R_ECX_32_1_8079:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_8088:bool = false
dsa_R_EIP_1_8089:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_8080:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp216"*/
addr 0xdcff67e3 @asm "sub    ecx,0x80" @tid "0"
  @context "R_ECX_32" = 0x414128a9, -1, u32, rw
  @context "R_EFLAGS" = 0x206, -1, u32, wr
label pc_0xdcff67e3
dsa_R_DF_1_8090:bool = false
dsa_T_t_1_8091:u32 = dsa_R_ECX_32_1_8079:u32
dsa_R_ECX_32_1_8092:u32 = dsa_R_ECX_32_1_8079:u32 - 0x80:u32
dsa_R_CF_1_8093:bool = dsa_T_t_1_8091:u32 < 0x80:u32
dsa_R_OF_1_8094:bool =
  high:bool((dsa_T_t_1_8091:u32 ^ 0x80:u32) &
            (dsa_T_t_1_8091:u32 ^ dsa_R_ECX_32_1_8092:u32))
dsa_R_AF_1_8095:bool =
  0x10:u32 ==
  (0x10:u32 & (dsa_R_ECX_32_1_8092:u32 ^ dsa_T_t_1_8091:u32 ^ 0x80:u32))
dsa_R_PF_3_8098:bool =
  ~low:bool(let dsa_T_acc_1_8096:u32 :=
                                         dsa_R_ECX_32_1_8092:u32 >> 4:u32 ^
                                         dsa_R_ECX_32_1_8092:u32 in
            let dsa_T_acc_2_8097:u32 :=
                                         dsa_T_acc_1_8096:u32 >> 2:u32 ^
                                         dsa_T_acc_1_8096:u32 in
            dsa_T_acc_2_8097:u32 >> 1:u32 ^ dsa_T_acc_2_8097:u32)
dsa_R_SF_1_8099:bool = high:bool(dsa_R_ECX_32_1_8092:u32)
dsa_R_ZF_1_8100:bool = 0:u32 == dsa_R_ECX_32_1_8092:u32
addr 0xdcff6816 @asm "jae    0x00000000dcff67a5" @tid "0"
  @context "R_EIP" = 0xdcff6816, 0, u32, rw
  @context "R_EFLAGS" = 0x202, -1, u32, rd
label pc_0xdcff6816
dsa_R_DF_1_8101:bool = false
dsa_R_EIP_1_8102:u32 = 0xdcff6816:u32
assert ~dsa_R_CF_1_8093:bool
/*Removed: cjmp ~R_CF_657:bool, 0xdcff67a5:u32, "nocjmp217"*/


