import R9_6_0Merge0
import R9_6_0Merge1
import R9_6_0Merge2
import R9_6_0Merge3
import R9_6_0Merge4
import R9_6_0Merge5
import R9_6_0Merge6
import R9_6_0Merge7
import R9_6_0Merge8
import R9_6_0Merge9
import R9_6_0Merge10
import R9_6_0Merge11
import R9_6_0Merge12
import R9_6_0Merge13
import R9_6_0Merge14
import R9_6_0Merge15
import R9_6_0Merge16
import R9_6_0Merge17
import R9_6_0Merge18
import R9_6_0Merge19
import R9_6_0Merge20
import R9_6_0Merge21
import R9_6_0Merge22
import R9_6_0Merge23
import R9_6_0Merge24
import R9_6_0Merge25
import R9_6_0Merge26
import R9_6_0Merge27
import R9_6_0Merge28
import R9_6_0Merge29
import R9_6_0Merge30
import R9_6_0Merge31
import R9_6_0Merge32
import R9_6_0Merge33
import R9_6_0Merge34
import R9_6_0Merge35
import R9_6_0Merge36
import R9_6_0Merge37
import R9_6_0Merge38
import R9_6_0Merge39
import R9_6_0Merge40
import R9_6_0Merge41
import R9_6_0Merge42
import R9_6_0Merge43
import R9_6_0Merge44
import R9_6_0Merge45
import R9_6_0Merge46
import R9_6_0Merge47
import R9_6_0Merge48
import R9_6_0Merge49
import R9_6_0Merge50
import R9_6_0Merge51
import R9_6_0Merge52
import R9_6_0Merge53
import R9_6_0Merge54
import R9_6_0Merge55
import R9_6_0Merge56
import R9_6_0Merge57
import R9_6_0Merge58
import R9_6_0Merge59
import R9_6_0Merge60
import R9_6_0Merge61
import R9_6_0Merge62
import R9_6_0Merge63
import R9_6_0Merge64
import R9_6_0Merge65
import R9_6_0Merge66
import R9_6_0Merge67
import R9_6_0Merge68
import R9_6_0Merge69
import R9_6_0Merge70
import R9_6_0Merge71
import R9_6_0Merge72
import R9_6_0Merge73
import R9_6_0Merge74
import R9_6_0Merge75
import R9_6_0Merge76
import R9_6_0Merge77
import R9_6_0Merge78
import R9_6_0Merge79
import R9_6_0Merge80
import R9_6_0Merge81
import R9_6_0Merge82
import R9_6_0Merge83
import R9_6_0Merge84
import R9_6_0Merge85
import R9_6_0Merge86
import R9_6_0Merge87
import R9_6_0Merge88
import R9_6_0Merge89
import R9_6_0Merge90
import R9_6_0Merge91
import R9_6_0Merge92
import R9_6_0Merge93
import R9_6_0Merge94
import R9_6_0Merge95
import R9_6_0Merge96
import R9_6_0Merge97
import R9_6_0Merge98
import R9_6_0Merge99
import R9_6_0Merge100
import R9_6_0Merge101
import R9_6_0Merge102
import R9_6_0Merge103
import R9_6_0Merge104
import R9_6_0Merge105
import R9_6_0Merge106
import R9_6_0Merge107
import R9_6_0Merge108
import R9_6_0Merge109
import R9_6_0Merge110
import R9_6_0Merge111
import R9_6_0Merge112
import R9_6_0Merge113
import R9_6_0Merge114
import R9_6_0Merge115
import R9_6_0Merge116
import R9_6_0Merge117
import R9_6_0Merge118
import R9_6_0Merge119
import R9_6_0Merge120
import R9_6_0Merge121
import R9_6_0Merge122
import R9_6_0Merge123
import R9_6_0Merge124
import R9_6_0Merge125
import R9_6_0Merge126
import R9_6_0Merge127
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_check : ∀ u : Fin 512, unionCheck 9 35 table u.val = true := by
  intro u
  by_cases h64 : u.val < 256
  ·
    by_cases h32 : u.val < 128
    ·
      by_cases h16 : u.val < 64
      ·
        by_cases h8 : u.val < 32
        ·
          by_cases h4 : u.val < 16
          ·
            by_cases h2 : u.val < 8
            ·
              by_cases h1 : u.val < 4
              ·
                have hb : u.val-0 < 4 := by omega
                have he : u.val-0+0 = u.val := by omega
                have hp := merge_check0 ⟨u.val-0,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-4 < 4 := by omega
                have he : u.val-4+4 = u.val := by omega
                have hp := merge_check1 ⟨u.val-4,hb⟩
                simpa only [he] using hp
            ·
              by_cases h3 : u.val < 12
              ·
                have hb : u.val-8 < 4 := by omega
                have he : u.val-8+8 = u.val := by omega
                have hp := merge_check2 ⟨u.val-8,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-12 < 4 := by omega
                have he : u.val-12+12 = u.val := by omega
                have hp := merge_check3 ⟨u.val-12,hb⟩
                simpa only [he] using hp
          ·
            by_cases h6 : u.val < 24
            ·
              by_cases h5 : u.val < 20
              ·
                have hb : u.val-16 < 4 := by omega
                have he : u.val-16+16 = u.val := by omega
                have hp := merge_check4 ⟨u.val-16,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-20 < 4 := by omega
                have he : u.val-20+20 = u.val := by omega
                have hp := merge_check5 ⟨u.val-20,hb⟩
                simpa only [he] using hp
            ·
              by_cases h7 : u.val < 28
              ·
                have hb : u.val-24 < 4 := by omega
                have he : u.val-24+24 = u.val := by omega
                have hp := merge_check6 ⟨u.val-24,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-28 < 4 := by omega
                have he : u.val-28+28 = u.val := by omega
                have hp := merge_check7 ⟨u.val-28,hb⟩
                simpa only [he] using hp
        ·
          by_cases h12 : u.val < 48
          ·
            by_cases h10 : u.val < 40
            ·
              by_cases h9 : u.val < 36
              ·
                have hb : u.val-32 < 4 := by omega
                have he : u.val-32+32 = u.val := by omega
                have hp := merge_check8 ⟨u.val-32,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-36 < 4 := by omega
                have he : u.val-36+36 = u.val := by omega
                have hp := merge_check9 ⟨u.val-36,hb⟩
                simpa only [he] using hp
            ·
              by_cases h11 : u.val < 44
              ·
                have hb : u.val-40 < 4 := by omega
                have he : u.val-40+40 = u.val := by omega
                have hp := merge_check10 ⟨u.val-40,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-44 < 4 := by omega
                have he : u.val-44+44 = u.val := by omega
                have hp := merge_check11 ⟨u.val-44,hb⟩
                simpa only [he] using hp
          ·
            by_cases h14 : u.val < 56
            ·
              by_cases h13 : u.val < 52
              ·
                have hb : u.val-48 < 4 := by omega
                have he : u.val-48+48 = u.val := by omega
                have hp := merge_check12 ⟨u.val-48,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-52 < 4 := by omega
                have he : u.val-52+52 = u.val := by omega
                have hp := merge_check13 ⟨u.val-52,hb⟩
                simpa only [he] using hp
            ·
              by_cases h15 : u.val < 60
              ·
                have hb : u.val-56 < 4 := by omega
                have he : u.val-56+56 = u.val := by omega
                have hp := merge_check14 ⟨u.val-56,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-60 < 4 := by omega
                have he : u.val-60+60 = u.val := by omega
                have hp := merge_check15 ⟨u.val-60,hb⟩
                simpa only [he] using hp
      ·
        by_cases h24 : u.val < 96
        ·
          by_cases h20 : u.val < 80
          ·
            by_cases h18 : u.val < 72
            ·
              by_cases h17 : u.val < 68
              ·
                have hb : u.val-64 < 4 := by omega
                have he : u.val-64+64 = u.val := by omega
                have hp := merge_check16 ⟨u.val-64,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-68 < 4 := by omega
                have he : u.val-68+68 = u.val := by omega
                have hp := merge_check17 ⟨u.val-68,hb⟩
                simpa only [he] using hp
            ·
              by_cases h19 : u.val < 76
              ·
                have hb : u.val-72 < 4 := by omega
                have he : u.val-72+72 = u.val := by omega
                have hp := merge_check18 ⟨u.val-72,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-76 < 4 := by omega
                have he : u.val-76+76 = u.val := by omega
                have hp := merge_check19 ⟨u.val-76,hb⟩
                simpa only [he] using hp
          ·
            by_cases h22 : u.val < 88
            ·
              by_cases h21 : u.val < 84
              ·
                have hb : u.val-80 < 4 := by omega
                have he : u.val-80+80 = u.val := by omega
                have hp := merge_check20 ⟨u.val-80,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-84 < 4 := by omega
                have he : u.val-84+84 = u.val := by omega
                have hp := merge_check21 ⟨u.val-84,hb⟩
                simpa only [he] using hp
            ·
              by_cases h23 : u.val < 92
              ·
                have hb : u.val-88 < 4 := by omega
                have he : u.val-88+88 = u.val := by omega
                have hp := merge_check22 ⟨u.val-88,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-92 < 4 := by omega
                have he : u.val-92+92 = u.val := by omega
                have hp := merge_check23 ⟨u.val-92,hb⟩
                simpa only [he] using hp
        ·
          by_cases h28 : u.val < 112
          ·
            by_cases h26 : u.val < 104
            ·
              by_cases h25 : u.val < 100
              ·
                have hb : u.val-96 < 4 := by omega
                have he : u.val-96+96 = u.val := by omega
                have hp := merge_check24 ⟨u.val-96,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-100 < 4 := by omega
                have he : u.val-100+100 = u.val := by omega
                have hp := merge_check25 ⟨u.val-100,hb⟩
                simpa only [he] using hp
            ·
              by_cases h27 : u.val < 108
              ·
                have hb : u.val-104 < 4 := by omega
                have he : u.val-104+104 = u.val := by omega
                have hp := merge_check26 ⟨u.val-104,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-108 < 4 := by omega
                have he : u.val-108+108 = u.val := by omega
                have hp := merge_check27 ⟨u.val-108,hb⟩
                simpa only [he] using hp
          ·
            by_cases h30 : u.val < 120
            ·
              by_cases h29 : u.val < 116
              ·
                have hb : u.val-112 < 4 := by omega
                have he : u.val-112+112 = u.val := by omega
                have hp := merge_check28 ⟨u.val-112,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-116 < 4 := by omega
                have he : u.val-116+116 = u.val := by omega
                have hp := merge_check29 ⟨u.val-116,hb⟩
                simpa only [he] using hp
            ·
              by_cases h31 : u.val < 124
              ·
                have hb : u.val-120 < 4 := by omega
                have he : u.val-120+120 = u.val := by omega
                have hp := merge_check30 ⟨u.val-120,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-124 < 4 := by omega
                have he : u.val-124+124 = u.val := by omega
                have hp := merge_check31 ⟨u.val-124,hb⟩
                simpa only [he] using hp
    ·
      by_cases h48 : u.val < 192
      ·
        by_cases h40 : u.val < 160
        ·
          by_cases h36 : u.val < 144
          ·
            by_cases h34 : u.val < 136
            ·
              by_cases h33 : u.val < 132
              ·
                have hb : u.val-128 < 4 := by omega
                have he : u.val-128+128 = u.val := by omega
                have hp := merge_check32 ⟨u.val-128,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-132 < 4 := by omega
                have he : u.val-132+132 = u.val := by omega
                have hp := merge_check33 ⟨u.val-132,hb⟩
                simpa only [he] using hp
            ·
              by_cases h35 : u.val < 140
              ·
                have hb : u.val-136 < 4 := by omega
                have he : u.val-136+136 = u.val := by omega
                have hp := merge_check34 ⟨u.val-136,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-140 < 4 := by omega
                have he : u.val-140+140 = u.val := by omega
                have hp := merge_check35 ⟨u.val-140,hb⟩
                simpa only [he] using hp
          ·
            by_cases h38 : u.val < 152
            ·
              by_cases h37 : u.val < 148
              ·
                have hb : u.val-144 < 4 := by omega
                have he : u.val-144+144 = u.val := by omega
                have hp := merge_check36 ⟨u.val-144,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-148 < 4 := by omega
                have he : u.val-148+148 = u.val := by omega
                have hp := merge_check37 ⟨u.val-148,hb⟩
                simpa only [he] using hp
            ·
              by_cases h39 : u.val < 156
              ·
                have hb : u.val-152 < 4 := by omega
                have he : u.val-152+152 = u.val := by omega
                have hp := merge_check38 ⟨u.val-152,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-156 < 4 := by omega
                have he : u.val-156+156 = u.val := by omega
                have hp := merge_check39 ⟨u.val-156,hb⟩
                simpa only [he] using hp
        ·
          by_cases h44 : u.val < 176
          ·
            by_cases h42 : u.val < 168
            ·
              by_cases h41 : u.val < 164
              ·
                have hb : u.val-160 < 4 := by omega
                have he : u.val-160+160 = u.val := by omega
                have hp := merge_check40 ⟨u.val-160,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-164 < 4 := by omega
                have he : u.val-164+164 = u.val := by omega
                have hp := merge_check41 ⟨u.val-164,hb⟩
                simpa only [he] using hp
            ·
              by_cases h43 : u.val < 172
              ·
                have hb : u.val-168 < 4 := by omega
                have he : u.val-168+168 = u.val := by omega
                have hp := merge_check42 ⟨u.val-168,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-172 < 4 := by omega
                have he : u.val-172+172 = u.val := by omega
                have hp := merge_check43 ⟨u.val-172,hb⟩
                simpa only [he] using hp
          ·
            by_cases h46 : u.val < 184
            ·
              by_cases h45 : u.val < 180
              ·
                have hb : u.val-176 < 4 := by omega
                have he : u.val-176+176 = u.val := by omega
                have hp := merge_check44 ⟨u.val-176,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-180 < 4 := by omega
                have he : u.val-180+180 = u.val := by omega
                have hp := merge_check45 ⟨u.val-180,hb⟩
                simpa only [he] using hp
            ·
              by_cases h47 : u.val < 188
              ·
                have hb : u.val-184 < 4 := by omega
                have he : u.val-184+184 = u.val := by omega
                have hp := merge_check46 ⟨u.val-184,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-188 < 4 := by omega
                have he : u.val-188+188 = u.val := by omega
                have hp := merge_check47 ⟨u.val-188,hb⟩
                simpa only [he] using hp
      ·
        by_cases h56 : u.val < 224
        ·
          by_cases h52 : u.val < 208
          ·
            by_cases h50 : u.val < 200
            ·
              by_cases h49 : u.val < 196
              ·
                have hb : u.val-192 < 4 := by omega
                have he : u.val-192+192 = u.val := by omega
                have hp := merge_check48 ⟨u.val-192,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-196 < 4 := by omega
                have he : u.val-196+196 = u.val := by omega
                have hp := merge_check49 ⟨u.val-196,hb⟩
                simpa only [he] using hp
            ·
              by_cases h51 : u.val < 204
              ·
                have hb : u.val-200 < 4 := by omega
                have he : u.val-200+200 = u.val := by omega
                have hp := merge_check50 ⟨u.val-200,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-204 < 4 := by omega
                have he : u.val-204+204 = u.val := by omega
                have hp := merge_check51 ⟨u.val-204,hb⟩
                simpa only [he] using hp
          ·
            by_cases h54 : u.val < 216
            ·
              by_cases h53 : u.val < 212
              ·
                have hb : u.val-208 < 4 := by omega
                have he : u.val-208+208 = u.val := by omega
                have hp := merge_check52 ⟨u.val-208,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-212 < 4 := by omega
                have he : u.val-212+212 = u.val := by omega
                have hp := merge_check53 ⟨u.val-212,hb⟩
                simpa only [he] using hp
            ·
              by_cases h55 : u.val < 220
              ·
                have hb : u.val-216 < 4 := by omega
                have he : u.val-216+216 = u.val := by omega
                have hp := merge_check54 ⟨u.val-216,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-220 < 4 := by omega
                have he : u.val-220+220 = u.val := by omega
                have hp := merge_check55 ⟨u.val-220,hb⟩
                simpa only [he] using hp
        ·
          by_cases h60 : u.val < 240
          ·
            by_cases h58 : u.val < 232
            ·
              by_cases h57 : u.val < 228
              ·
                have hb : u.val-224 < 4 := by omega
                have he : u.val-224+224 = u.val := by omega
                have hp := merge_check56 ⟨u.val-224,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-228 < 4 := by omega
                have he : u.val-228+228 = u.val := by omega
                have hp := merge_check57 ⟨u.val-228,hb⟩
                simpa only [he] using hp
            ·
              by_cases h59 : u.val < 236
              ·
                have hb : u.val-232 < 4 := by omega
                have he : u.val-232+232 = u.val := by omega
                have hp := merge_check58 ⟨u.val-232,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-236 < 4 := by omega
                have he : u.val-236+236 = u.val := by omega
                have hp := merge_check59 ⟨u.val-236,hb⟩
                simpa only [he] using hp
          ·
            by_cases h62 : u.val < 248
            ·
              by_cases h61 : u.val < 244
              ·
                have hb : u.val-240 < 4 := by omega
                have he : u.val-240+240 = u.val := by omega
                have hp := merge_check60 ⟨u.val-240,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-244 < 4 := by omega
                have he : u.val-244+244 = u.val := by omega
                have hp := merge_check61 ⟨u.val-244,hb⟩
                simpa only [he] using hp
            ·
              by_cases h63 : u.val < 252
              ·
                have hb : u.val-248 < 4 := by omega
                have he : u.val-248+248 = u.val := by omega
                have hp := merge_check62 ⟨u.val-248,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-252 < 4 := by omega
                have he : u.val-252+252 = u.val := by omega
                have hp := merge_check63 ⟨u.val-252,hb⟩
                simpa only [he] using hp
  ·
    by_cases h96 : u.val < 384
    ·
      by_cases h80 : u.val < 320
      ·
        by_cases h72 : u.val < 288
        ·
          by_cases h68 : u.val < 272
          ·
            by_cases h66 : u.val < 264
            ·
              by_cases h65 : u.val < 260
              ·
                have hb : u.val-256 < 4 := by omega
                have he : u.val-256+256 = u.val := by omega
                have hp := merge_check64 ⟨u.val-256,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-260 < 4 := by omega
                have he : u.val-260+260 = u.val := by omega
                have hp := merge_check65 ⟨u.val-260,hb⟩
                simpa only [he] using hp
            ·
              by_cases h67 : u.val < 268
              ·
                have hb : u.val-264 < 4 := by omega
                have he : u.val-264+264 = u.val := by omega
                have hp := merge_check66 ⟨u.val-264,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-268 < 4 := by omega
                have he : u.val-268+268 = u.val := by omega
                have hp := merge_check67 ⟨u.val-268,hb⟩
                simpa only [he] using hp
          ·
            by_cases h70 : u.val < 280
            ·
              by_cases h69 : u.val < 276
              ·
                have hb : u.val-272 < 4 := by omega
                have he : u.val-272+272 = u.val := by omega
                have hp := merge_check68 ⟨u.val-272,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-276 < 4 := by omega
                have he : u.val-276+276 = u.val := by omega
                have hp := merge_check69 ⟨u.val-276,hb⟩
                simpa only [he] using hp
            ·
              by_cases h71 : u.val < 284
              ·
                have hb : u.val-280 < 4 := by omega
                have he : u.val-280+280 = u.val := by omega
                have hp := merge_check70 ⟨u.val-280,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-284 < 4 := by omega
                have he : u.val-284+284 = u.val := by omega
                have hp := merge_check71 ⟨u.val-284,hb⟩
                simpa only [he] using hp
        ·
          by_cases h76 : u.val < 304
          ·
            by_cases h74 : u.val < 296
            ·
              by_cases h73 : u.val < 292
              ·
                have hb : u.val-288 < 4 := by omega
                have he : u.val-288+288 = u.val := by omega
                have hp := merge_check72 ⟨u.val-288,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-292 < 4 := by omega
                have he : u.val-292+292 = u.val := by omega
                have hp := merge_check73 ⟨u.val-292,hb⟩
                simpa only [he] using hp
            ·
              by_cases h75 : u.val < 300
              ·
                have hb : u.val-296 < 4 := by omega
                have he : u.val-296+296 = u.val := by omega
                have hp := merge_check74 ⟨u.val-296,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-300 < 4 := by omega
                have he : u.val-300+300 = u.val := by omega
                have hp := merge_check75 ⟨u.val-300,hb⟩
                simpa only [he] using hp
          ·
            by_cases h78 : u.val < 312
            ·
              by_cases h77 : u.val < 308
              ·
                have hb : u.val-304 < 4 := by omega
                have he : u.val-304+304 = u.val := by omega
                have hp := merge_check76 ⟨u.val-304,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-308 < 4 := by omega
                have he : u.val-308+308 = u.val := by omega
                have hp := merge_check77 ⟨u.val-308,hb⟩
                simpa only [he] using hp
            ·
              by_cases h79 : u.val < 316
              ·
                have hb : u.val-312 < 4 := by omega
                have he : u.val-312+312 = u.val := by omega
                have hp := merge_check78 ⟨u.val-312,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-316 < 4 := by omega
                have he : u.val-316+316 = u.val := by omega
                have hp := merge_check79 ⟨u.val-316,hb⟩
                simpa only [he] using hp
      ·
        by_cases h88 : u.val < 352
        ·
          by_cases h84 : u.val < 336
          ·
            by_cases h82 : u.val < 328
            ·
              by_cases h81 : u.val < 324
              ·
                have hb : u.val-320 < 4 := by omega
                have he : u.val-320+320 = u.val := by omega
                have hp := merge_check80 ⟨u.val-320,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-324 < 4 := by omega
                have he : u.val-324+324 = u.val := by omega
                have hp := merge_check81 ⟨u.val-324,hb⟩
                simpa only [he] using hp
            ·
              by_cases h83 : u.val < 332
              ·
                have hb : u.val-328 < 4 := by omega
                have he : u.val-328+328 = u.val := by omega
                have hp := merge_check82 ⟨u.val-328,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-332 < 4 := by omega
                have he : u.val-332+332 = u.val := by omega
                have hp := merge_check83 ⟨u.val-332,hb⟩
                simpa only [he] using hp
          ·
            by_cases h86 : u.val < 344
            ·
              by_cases h85 : u.val < 340
              ·
                have hb : u.val-336 < 4 := by omega
                have he : u.val-336+336 = u.val := by omega
                have hp := merge_check84 ⟨u.val-336,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-340 < 4 := by omega
                have he : u.val-340+340 = u.val := by omega
                have hp := merge_check85 ⟨u.val-340,hb⟩
                simpa only [he] using hp
            ·
              by_cases h87 : u.val < 348
              ·
                have hb : u.val-344 < 4 := by omega
                have he : u.val-344+344 = u.val := by omega
                have hp := merge_check86 ⟨u.val-344,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-348 < 4 := by omega
                have he : u.val-348+348 = u.val := by omega
                have hp := merge_check87 ⟨u.val-348,hb⟩
                simpa only [he] using hp
        ·
          by_cases h92 : u.val < 368
          ·
            by_cases h90 : u.val < 360
            ·
              by_cases h89 : u.val < 356
              ·
                have hb : u.val-352 < 4 := by omega
                have he : u.val-352+352 = u.val := by omega
                have hp := merge_check88 ⟨u.val-352,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-356 < 4 := by omega
                have he : u.val-356+356 = u.val := by omega
                have hp := merge_check89 ⟨u.val-356,hb⟩
                simpa only [he] using hp
            ·
              by_cases h91 : u.val < 364
              ·
                have hb : u.val-360 < 4 := by omega
                have he : u.val-360+360 = u.val := by omega
                have hp := merge_check90 ⟨u.val-360,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-364 < 4 := by omega
                have he : u.val-364+364 = u.val := by omega
                have hp := merge_check91 ⟨u.val-364,hb⟩
                simpa only [he] using hp
          ·
            by_cases h94 : u.val < 376
            ·
              by_cases h93 : u.val < 372
              ·
                have hb : u.val-368 < 4 := by omega
                have he : u.val-368+368 = u.val := by omega
                have hp := merge_check92 ⟨u.val-368,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-372 < 4 := by omega
                have he : u.val-372+372 = u.val := by omega
                have hp := merge_check93 ⟨u.val-372,hb⟩
                simpa only [he] using hp
            ·
              by_cases h95 : u.val < 380
              ·
                have hb : u.val-376 < 4 := by omega
                have he : u.val-376+376 = u.val := by omega
                have hp := merge_check94 ⟨u.val-376,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-380 < 4 := by omega
                have he : u.val-380+380 = u.val := by omega
                have hp := merge_check95 ⟨u.val-380,hb⟩
                simpa only [he] using hp
    ·
      by_cases h112 : u.val < 448
      ·
        by_cases h104 : u.val < 416
        ·
          by_cases h100 : u.val < 400
          ·
            by_cases h98 : u.val < 392
            ·
              by_cases h97 : u.val < 388
              ·
                have hb : u.val-384 < 4 := by omega
                have he : u.val-384+384 = u.val := by omega
                have hp := merge_check96 ⟨u.val-384,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-388 < 4 := by omega
                have he : u.val-388+388 = u.val := by omega
                have hp := merge_check97 ⟨u.val-388,hb⟩
                simpa only [he] using hp
            ·
              by_cases h99 : u.val < 396
              ·
                have hb : u.val-392 < 4 := by omega
                have he : u.val-392+392 = u.val := by omega
                have hp := merge_check98 ⟨u.val-392,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-396 < 4 := by omega
                have he : u.val-396+396 = u.val := by omega
                have hp := merge_check99 ⟨u.val-396,hb⟩
                simpa only [he] using hp
          ·
            by_cases h102 : u.val < 408
            ·
              by_cases h101 : u.val < 404
              ·
                have hb : u.val-400 < 4 := by omega
                have he : u.val-400+400 = u.val := by omega
                have hp := merge_check100 ⟨u.val-400,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-404 < 4 := by omega
                have he : u.val-404+404 = u.val := by omega
                have hp := merge_check101 ⟨u.val-404,hb⟩
                simpa only [he] using hp
            ·
              by_cases h103 : u.val < 412
              ·
                have hb : u.val-408 < 4 := by omega
                have he : u.val-408+408 = u.val := by omega
                have hp := merge_check102 ⟨u.val-408,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-412 < 4 := by omega
                have he : u.val-412+412 = u.val := by omega
                have hp := merge_check103 ⟨u.val-412,hb⟩
                simpa only [he] using hp
        ·
          by_cases h108 : u.val < 432
          ·
            by_cases h106 : u.val < 424
            ·
              by_cases h105 : u.val < 420
              ·
                have hb : u.val-416 < 4 := by omega
                have he : u.val-416+416 = u.val := by omega
                have hp := merge_check104 ⟨u.val-416,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-420 < 4 := by omega
                have he : u.val-420+420 = u.val := by omega
                have hp := merge_check105 ⟨u.val-420,hb⟩
                simpa only [he] using hp
            ·
              by_cases h107 : u.val < 428
              ·
                have hb : u.val-424 < 4 := by omega
                have he : u.val-424+424 = u.val := by omega
                have hp := merge_check106 ⟨u.val-424,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-428 < 4 := by omega
                have he : u.val-428+428 = u.val := by omega
                have hp := merge_check107 ⟨u.val-428,hb⟩
                simpa only [he] using hp
          ·
            by_cases h110 : u.val < 440
            ·
              by_cases h109 : u.val < 436
              ·
                have hb : u.val-432 < 4 := by omega
                have he : u.val-432+432 = u.val := by omega
                have hp := merge_check108 ⟨u.val-432,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-436 < 4 := by omega
                have he : u.val-436+436 = u.val := by omega
                have hp := merge_check109 ⟨u.val-436,hb⟩
                simpa only [he] using hp
            ·
              by_cases h111 : u.val < 444
              ·
                have hb : u.val-440 < 4 := by omega
                have he : u.val-440+440 = u.val := by omega
                have hp := merge_check110 ⟨u.val-440,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-444 < 4 := by omega
                have he : u.val-444+444 = u.val := by omega
                have hp := merge_check111 ⟨u.val-444,hb⟩
                simpa only [he] using hp
      ·
        by_cases h120 : u.val < 480
        ·
          by_cases h116 : u.val < 464
          ·
            by_cases h114 : u.val < 456
            ·
              by_cases h113 : u.val < 452
              ·
                have hb : u.val-448 < 4 := by omega
                have he : u.val-448+448 = u.val := by omega
                have hp := merge_check112 ⟨u.val-448,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-452 < 4 := by omega
                have he : u.val-452+452 = u.val := by omega
                have hp := merge_check113 ⟨u.val-452,hb⟩
                simpa only [he] using hp
            ·
              by_cases h115 : u.val < 460
              ·
                have hb : u.val-456 < 4 := by omega
                have he : u.val-456+456 = u.val := by omega
                have hp := merge_check114 ⟨u.val-456,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-460 < 4 := by omega
                have he : u.val-460+460 = u.val := by omega
                have hp := merge_check115 ⟨u.val-460,hb⟩
                simpa only [he] using hp
          ·
            by_cases h118 : u.val < 472
            ·
              by_cases h117 : u.val < 468
              ·
                have hb : u.val-464 < 4 := by omega
                have he : u.val-464+464 = u.val := by omega
                have hp := merge_check116 ⟨u.val-464,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-468 < 4 := by omega
                have he : u.val-468+468 = u.val := by omega
                have hp := merge_check117 ⟨u.val-468,hb⟩
                simpa only [he] using hp
            ·
              by_cases h119 : u.val < 476
              ·
                have hb : u.val-472 < 4 := by omega
                have he : u.val-472+472 = u.val := by omega
                have hp := merge_check118 ⟨u.val-472,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-476 < 4 := by omega
                have he : u.val-476+476 = u.val := by omega
                have hp := merge_check119 ⟨u.val-476,hb⟩
                simpa only [he] using hp
        ·
          by_cases h124 : u.val < 496
          ·
            by_cases h122 : u.val < 488
            ·
              by_cases h121 : u.val < 484
              ·
                have hb : u.val-480 < 4 := by omega
                have he : u.val-480+480 = u.val := by omega
                have hp := merge_check120 ⟨u.val-480,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-484 < 4 := by omega
                have he : u.val-484+484 = u.val := by omega
                have hp := merge_check121 ⟨u.val-484,hb⟩
                simpa only [he] using hp
            ·
              by_cases h123 : u.val < 492
              ·
                have hb : u.val-488 < 4 := by omega
                have he : u.val-488+488 = u.val := by omega
                have hp := merge_check122 ⟨u.val-488,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-492 < 4 := by omega
                have he : u.val-492+492 = u.val := by omega
                have hp := merge_check123 ⟨u.val-492,hb⟩
                simpa only [he] using hp
          ·
            by_cases h126 : u.val < 504
            ·
              by_cases h125 : u.val < 500
              ·
                have hb : u.val-496 < 4 := by omega
                have he : u.val-496+496 = u.val := by omega
                have hp := merge_check124 ⟨u.val-496,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-500 < 4 := by omega
                have he : u.val-500+500 = u.val := by omega
                have hp := merge_check125 ⟨u.val-500,hb⟩
                simpa only [he] using hp
            ·
              by_cases h127 : u.val < 508
              ·
                have hb : u.val-504 < 4 := by omega
                have he : u.val-504+504 = u.val := by omega
                have hp := merge_check126 ⟨u.val-504,hb⟩
                simpa only [he] using hp
              ·
                have hb : u.val-508 < 4 := by omega
                have he : u.val-508+508 = u.val := by omega
                have hp := merge_check127 ⟨u.val-508,hb⟩
                simpa only [he] using hp

end R9_6_0
