import R9_6_0Edge0
import R9_6_0Edge1
import R9_6_0Edge2
import R9_6_0Edge3
import R9_6_0Edge4
import R9_6_0Edge5
import R9_6_0Edge6
import R9_6_0Edge7
import R9_6_0Edge8
import R9_6_0Edge9
import R9_6_0Edge10
import R9_6_0Edge11
import R9_6_0Edge12
import R9_6_0Edge13
import R9_6_0Edge14
import R9_6_0Edge15
import R9_6_0Edge16
import R9_6_0Edge17
import R9_6_0Edge18
import R9_6_0Edge19
import R9_6_0Edge20
import R9_6_0Edge21
import R9_6_0Edge22
import R9_6_0Edge23
import R9_6_0Edge24
import R9_6_0Edge25
import R9_6_0Edge26
import R9_6_0Edge27
import R9_6_0Edge28
import R9_6_0Edge29
import R9_6_0Edge30
import R9_6_0Edge31
import R9_6_0Edge32
import R9_6_0Edge33
import R9_6_0Edge34
import R9_6_0Edge35
import R9_6_0Edge36
import R9_6_0Edge37
import R9_6_0Edge38
import R9_6_0Edge39
import R9_6_0Edge40
import R9_6_0Edge41
import R9_6_0Edge42
import R9_6_0Edge43
import R9_6_0Edge44
import R9_6_0Edge45
import R9_6_0Edge46
import R9_6_0Edge47
import R9_6_0Edge48
import R9_6_0Edge49
import R9_6_0Edge50
import R9_6_0Edge51
import R9_6_0Edge52
import R9_6_0Edge53
import R9_6_0Edge54
import R9_6_0Edge55
import R9_6_0Edge56
import R9_6_0Edge57
import R9_6_0Edge58
import R9_6_0Edge59
import R9_6_0Edge60
import R9_6_0Edge61
import R9_6_0Edge62
import R9_6_0Edge63
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem edge_check : ∀ m : Fin 512, m.val ≠ 0 → ∀ vw ∈ edges,
  digit (table m.val) vw.1.val ≤ digit (table m.val) vw.2.val + 1 := by
  intro m
  by_cases h32 : m.val < 256
  ·
    by_cases h16 : m.val < 128
    ·
      by_cases h8 : m.val < 64
      ·
        by_cases h4 : m.val < 32
        ·
          by_cases h2 : m.val < 16
          ·
            by_cases h1 : m.val < 8
            ·
              have hb : m.val-0 < 8 := by omega
              have he : m.val-0+0 = m.val := by omega
              have hp := edge_check0 ⟨m.val-0,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-8 < 8 := by omega
              have he : m.val-8+8 = m.val := by omega
              have hp := edge_check1 ⟨m.val-8,hb⟩
              simpa only [he] using hp
          ·
            by_cases h3 : m.val < 24
            ·
              have hb : m.val-16 < 8 := by omega
              have he : m.val-16+16 = m.val := by omega
              have hp := edge_check2 ⟨m.val-16,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-24 < 8 := by omega
              have he : m.val-24+24 = m.val := by omega
              have hp := edge_check3 ⟨m.val-24,hb⟩
              simpa only [he] using hp
        ·
          by_cases h6 : m.val < 48
          ·
            by_cases h5 : m.val < 40
            ·
              have hb : m.val-32 < 8 := by omega
              have he : m.val-32+32 = m.val := by omega
              have hp := edge_check4 ⟨m.val-32,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-40 < 8 := by omega
              have he : m.val-40+40 = m.val := by omega
              have hp := edge_check5 ⟨m.val-40,hb⟩
              simpa only [he] using hp
          ·
            by_cases h7 : m.val < 56
            ·
              have hb : m.val-48 < 8 := by omega
              have he : m.val-48+48 = m.val := by omega
              have hp := edge_check6 ⟨m.val-48,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-56 < 8 := by omega
              have he : m.val-56+56 = m.val := by omega
              have hp := edge_check7 ⟨m.val-56,hb⟩
              simpa only [he] using hp
      ·
        by_cases h12 : m.val < 96
        ·
          by_cases h10 : m.val < 80
          ·
            by_cases h9 : m.val < 72
            ·
              have hb : m.val-64 < 8 := by omega
              have he : m.val-64+64 = m.val := by omega
              have hp := edge_check8 ⟨m.val-64,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-72 < 8 := by omega
              have he : m.val-72+72 = m.val := by omega
              have hp := edge_check9 ⟨m.val-72,hb⟩
              simpa only [he] using hp
          ·
            by_cases h11 : m.val < 88
            ·
              have hb : m.val-80 < 8 := by omega
              have he : m.val-80+80 = m.val := by omega
              have hp := edge_check10 ⟨m.val-80,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-88 < 8 := by omega
              have he : m.val-88+88 = m.val := by omega
              have hp := edge_check11 ⟨m.val-88,hb⟩
              simpa only [he] using hp
        ·
          by_cases h14 : m.val < 112
          ·
            by_cases h13 : m.val < 104
            ·
              have hb : m.val-96 < 8 := by omega
              have he : m.val-96+96 = m.val := by omega
              have hp := edge_check12 ⟨m.val-96,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-104 < 8 := by omega
              have he : m.val-104+104 = m.val := by omega
              have hp := edge_check13 ⟨m.val-104,hb⟩
              simpa only [he] using hp
          ·
            by_cases h15 : m.val < 120
            ·
              have hb : m.val-112 < 8 := by omega
              have he : m.val-112+112 = m.val := by omega
              have hp := edge_check14 ⟨m.val-112,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-120 < 8 := by omega
              have he : m.val-120+120 = m.val := by omega
              have hp := edge_check15 ⟨m.val-120,hb⟩
              simpa only [he] using hp
    ·
      by_cases h24 : m.val < 192
      ·
        by_cases h20 : m.val < 160
        ·
          by_cases h18 : m.val < 144
          ·
            by_cases h17 : m.val < 136
            ·
              have hb : m.val-128 < 8 := by omega
              have he : m.val-128+128 = m.val := by omega
              have hp := edge_check16 ⟨m.val-128,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-136 < 8 := by omega
              have he : m.val-136+136 = m.val := by omega
              have hp := edge_check17 ⟨m.val-136,hb⟩
              simpa only [he] using hp
          ·
            by_cases h19 : m.val < 152
            ·
              have hb : m.val-144 < 8 := by omega
              have he : m.val-144+144 = m.val := by omega
              have hp := edge_check18 ⟨m.val-144,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-152 < 8 := by omega
              have he : m.val-152+152 = m.val := by omega
              have hp := edge_check19 ⟨m.val-152,hb⟩
              simpa only [he] using hp
        ·
          by_cases h22 : m.val < 176
          ·
            by_cases h21 : m.val < 168
            ·
              have hb : m.val-160 < 8 := by omega
              have he : m.val-160+160 = m.val := by omega
              have hp := edge_check20 ⟨m.val-160,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-168 < 8 := by omega
              have he : m.val-168+168 = m.val := by omega
              have hp := edge_check21 ⟨m.val-168,hb⟩
              simpa only [he] using hp
          ·
            by_cases h23 : m.val < 184
            ·
              have hb : m.val-176 < 8 := by omega
              have he : m.val-176+176 = m.val := by omega
              have hp := edge_check22 ⟨m.val-176,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-184 < 8 := by omega
              have he : m.val-184+184 = m.val := by omega
              have hp := edge_check23 ⟨m.val-184,hb⟩
              simpa only [he] using hp
      ·
        by_cases h28 : m.val < 224
        ·
          by_cases h26 : m.val < 208
          ·
            by_cases h25 : m.val < 200
            ·
              have hb : m.val-192 < 8 := by omega
              have he : m.val-192+192 = m.val := by omega
              have hp := edge_check24 ⟨m.val-192,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-200 < 8 := by omega
              have he : m.val-200+200 = m.val := by omega
              have hp := edge_check25 ⟨m.val-200,hb⟩
              simpa only [he] using hp
          ·
            by_cases h27 : m.val < 216
            ·
              have hb : m.val-208 < 8 := by omega
              have he : m.val-208+208 = m.val := by omega
              have hp := edge_check26 ⟨m.val-208,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-216 < 8 := by omega
              have he : m.val-216+216 = m.val := by omega
              have hp := edge_check27 ⟨m.val-216,hb⟩
              simpa only [he] using hp
        ·
          by_cases h30 : m.val < 240
          ·
            by_cases h29 : m.val < 232
            ·
              have hb : m.val-224 < 8 := by omega
              have he : m.val-224+224 = m.val := by omega
              have hp := edge_check28 ⟨m.val-224,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-232 < 8 := by omega
              have he : m.val-232+232 = m.val := by omega
              have hp := edge_check29 ⟨m.val-232,hb⟩
              simpa only [he] using hp
          ·
            by_cases h31 : m.val < 248
            ·
              have hb : m.val-240 < 8 := by omega
              have he : m.val-240+240 = m.val := by omega
              have hp := edge_check30 ⟨m.val-240,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-248 < 8 := by omega
              have he : m.val-248+248 = m.val := by omega
              have hp := edge_check31 ⟨m.val-248,hb⟩
              simpa only [he] using hp
  ·
    by_cases h48 : m.val < 384
    ·
      by_cases h40 : m.val < 320
      ·
        by_cases h36 : m.val < 288
        ·
          by_cases h34 : m.val < 272
          ·
            by_cases h33 : m.val < 264
            ·
              have hb : m.val-256 < 8 := by omega
              have he : m.val-256+256 = m.val := by omega
              have hp := edge_check32 ⟨m.val-256,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-264 < 8 := by omega
              have he : m.val-264+264 = m.val := by omega
              have hp := edge_check33 ⟨m.val-264,hb⟩
              simpa only [he] using hp
          ·
            by_cases h35 : m.val < 280
            ·
              have hb : m.val-272 < 8 := by omega
              have he : m.val-272+272 = m.val := by omega
              have hp := edge_check34 ⟨m.val-272,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-280 < 8 := by omega
              have he : m.val-280+280 = m.val := by omega
              have hp := edge_check35 ⟨m.val-280,hb⟩
              simpa only [he] using hp
        ·
          by_cases h38 : m.val < 304
          ·
            by_cases h37 : m.val < 296
            ·
              have hb : m.val-288 < 8 := by omega
              have he : m.val-288+288 = m.val := by omega
              have hp := edge_check36 ⟨m.val-288,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-296 < 8 := by omega
              have he : m.val-296+296 = m.val := by omega
              have hp := edge_check37 ⟨m.val-296,hb⟩
              simpa only [he] using hp
          ·
            by_cases h39 : m.val < 312
            ·
              have hb : m.val-304 < 8 := by omega
              have he : m.val-304+304 = m.val := by omega
              have hp := edge_check38 ⟨m.val-304,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-312 < 8 := by omega
              have he : m.val-312+312 = m.val := by omega
              have hp := edge_check39 ⟨m.val-312,hb⟩
              simpa only [he] using hp
      ·
        by_cases h44 : m.val < 352
        ·
          by_cases h42 : m.val < 336
          ·
            by_cases h41 : m.val < 328
            ·
              have hb : m.val-320 < 8 := by omega
              have he : m.val-320+320 = m.val := by omega
              have hp := edge_check40 ⟨m.val-320,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-328 < 8 := by omega
              have he : m.val-328+328 = m.val := by omega
              have hp := edge_check41 ⟨m.val-328,hb⟩
              simpa only [he] using hp
          ·
            by_cases h43 : m.val < 344
            ·
              have hb : m.val-336 < 8 := by omega
              have he : m.val-336+336 = m.val := by omega
              have hp := edge_check42 ⟨m.val-336,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-344 < 8 := by omega
              have he : m.val-344+344 = m.val := by omega
              have hp := edge_check43 ⟨m.val-344,hb⟩
              simpa only [he] using hp
        ·
          by_cases h46 : m.val < 368
          ·
            by_cases h45 : m.val < 360
            ·
              have hb : m.val-352 < 8 := by omega
              have he : m.val-352+352 = m.val := by omega
              have hp := edge_check44 ⟨m.val-352,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-360 < 8 := by omega
              have he : m.val-360+360 = m.val := by omega
              have hp := edge_check45 ⟨m.val-360,hb⟩
              simpa only [he] using hp
          ·
            by_cases h47 : m.val < 376
            ·
              have hb : m.val-368 < 8 := by omega
              have he : m.val-368+368 = m.val := by omega
              have hp := edge_check46 ⟨m.val-368,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-376 < 8 := by omega
              have he : m.val-376+376 = m.val := by omega
              have hp := edge_check47 ⟨m.val-376,hb⟩
              simpa only [he] using hp
    ·
      by_cases h56 : m.val < 448
      ·
        by_cases h52 : m.val < 416
        ·
          by_cases h50 : m.val < 400
          ·
            by_cases h49 : m.val < 392
            ·
              have hb : m.val-384 < 8 := by omega
              have he : m.val-384+384 = m.val := by omega
              have hp := edge_check48 ⟨m.val-384,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-392 < 8 := by omega
              have he : m.val-392+392 = m.val := by omega
              have hp := edge_check49 ⟨m.val-392,hb⟩
              simpa only [he] using hp
          ·
            by_cases h51 : m.val < 408
            ·
              have hb : m.val-400 < 8 := by omega
              have he : m.val-400+400 = m.val := by omega
              have hp := edge_check50 ⟨m.val-400,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-408 < 8 := by omega
              have he : m.val-408+408 = m.val := by omega
              have hp := edge_check51 ⟨m.val-408,hb⟩
              simpa only [he] using hp
        ·
          by_cases h54 : m.val < 432
          ·
            by_cases h53 : m.val < 424
            ·
              have hb : m.val-416 < 8 := by omega
              have he : m.val-416+416 = m.val := by omega
              have hp := edge_check52 ⟨m.val-416,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-424 < 8 := by omega
              have he : m.val-424+424 = m.val := by omega
              have hp := edge_check53 ⟨m.val-424,hb⟩
              simpa only [he] using hp
          ·
            by_cases h55 : m.val < 440
            ·
              have hb : m.val-432 < 8 := by omega
              have he : m.val-432+432 = m.val := by omega
              have hp := edge_check54 ⟨m.val-432,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-440 < 8 := by omega
              have he : m.val-440+440 = m.val := by omega
              have hp := edge_check55 ⟨m.val-440,hb⟩
              simpa only [he] using hp
      ·
        by_cases h60 : m.val < 480
        ·
          by_cases h58 : m.val < 464
          ·
            by_cases h57 : m.val < 456
            ·
              have hb : m.val-448 < 8 := by omega
              have he : m.val-448+448 = m.val := by omega
              have hp := edge_check56 ⟨m.val-448,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-456 < 8 := by omega
              have he : m.val-456+456 = m.val := by omega
              have hp := edge_check57 ⟨m.val-456,hb⟩
              simpa only [he] using hp
          ·
            by_cases h59 : m.val < 472
            ·
              have hb : m.val-464 < 8 := by omega
              have he : m.val-464+464 = m.val := by omega
              have hp := edge_check58 ⟨m.val-464,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-472 < 8 := by omega
              have he : m.val-472+472 = m.val := by omega
              have hp := edge_check59 ⟨m.val-472,hb⟩
              simpa only [he] using hp
        ·
          by_cases h62 : m.val < 496
          ·
            by_cases h61 : m.val < 488
            ·
              have hb : m.val-480 < 8 := by omega
              have he : m.val-480+480 = m.val := by omega
              have hp := edge_check60 ⟨m.val-480,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-488 < 8 := by omega
              have he : m.val-488+488 = m.val := by omega
              have hp := edge_check61 ⟨m.val-488,hb⟩
              simpa only [he] using hp
          ·
            by_cases h63 : m.val < 504
            ·
              have hb : m.val-496 < 8 := by omega
              have he : m.val-496+496 = m.val := by omega
              have hp := edge_check62 ⟨m.val-496,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-504 < 8 := by omega
              have he : m.val-504+504 = m.val := by omega
              have hp := edge_check63 ⟨m.val-504,hb⟩
              simpa only [he] using hp

end R9_6_0
