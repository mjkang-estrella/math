import R6_6_1EdgeB0
import R6_6_1EdgeB1
import R6_6_1EdgeB2
import R6_6_1EdgeB3
import R6_6_1EdgeB4
import R6_6_1EdgeB5
import R6_6_1EdgeB6
import R6_6_1EdgeB7
import R6_6_1EdgeB8
import R6_6_1EdgeB9
import R6_6_1EdgeB10
import R6_6_1EdgeB11
import R6_6_1EdgeB12
import R6_6_1EdgeB13
import R6_6_1EdgeB14
import R6_6_1EdgeB15
import R6_6_1EdgeB16
import R6_6_1EdgeB17
import R6_6_1EdgeB18
import R6_6_1EdgeB19
import R6_6_1EdgeB20
import R6_6_1EdgeB21
import R6_6_1EdgeB22
import R6_6_1EdgeB23
import R6_6_1EdgeB24
import R6_6_1EdgeB25
import R6_6_1EdgeB26
import R6_6_1EdgeB27
import R6_6_1EdgeB28
import R6_6_1EdgeB29
import R6_6_1EdgeB30
import R6_6_1EdgeB31
import R6_6_1EdgeB32
import R6_6_1EdgeB33
import R6_6_1EdgeB34
import R6_6_1EdgeB35
import R6_6_1EdgeB36
import R6_6_1EdgeB37
import R6_6_1EdgeB38
import R6_6_1EdgeB39
import R6_6_1EdgeB40
import R6_6_1EdgeB41
import R6_6_1EdgeB42
import R6_6_1EdgeB43
import R6_6_1EdgeB44
import R6_6_1EdgeB45
import R6_6_1EdgeB46
import R6_6_1EdgeB47
import R6_6_1EdgeB48
import R6_6_1EdgeB49
import R6_6_1EdgeB50
import R6_6_1EdgeB51
import R6_6_1EdgeB52
import R6_6_1EdgeB53
import R6_6_1EdgeB54
import R6_6_1EdgeB55
import R6_6_1EdgeB56
import R6_6_1EdgeB57
import R6_6_1EdgeB58
import R6_6_1EdgeB59
import R6_6_1EdgeB60
import R6_6_1EdgeB61
import R6_6_1EdgeB62
import R6_6_1EdgeB63
import R6_6_1EdgeB64
import R6_6_1EdgeB65
import R6_6_1EdgeB66
import R6_6_1EdgeB67
import R6_6_1EdgeB68
import R6_6_1EdgeB69
import R6_6_1EdgeB70
import R6_6_1EdgeB71
import R6_6_1EdgeB72
import R6_6_1EdgeB73
import R6_6_1EdgeB74
import R6_6_1EdgeB75
import R6_6_1EdgeB76
import R6_6_1EdgeB77
import R6_6_1EdgeB78
import R6_6_1EdgeB79
import R6_6_1EdgeB80
import R6_6_1EdgeB81
import R6_6_1EdgeB82
import R6_6_1EdgeB83
import R6_6_1EdgeB84
import R6_6_1EdgeB85
import R6_6_1EdgeB86
import R6_6_1EdgeB87
import R6_6_1EdgeB88
import R6_6_1EdgeB89
import R6_6_1EdgeB90
import R6_6_1EdgeB91
import R6_6_1EdgeB92
import R6_6_1EdgeB93
import R6_6_1EdgeB94
import R6_6_1EdgeB95
import R6_6_1EdgeB96
import R6_6_1EdgeB97
import R6_6_1EdgeB98
import R6_6_1EdgeB99
import R6_6_1EdgeB100
import R6_6_1EdgeB101
import R6_6_1EdgeB102
import R6_6_1EdgeB103
import R6_6_1EdgeB104
import R6_6_1EdgeB105
import R6_6_1EdgeB106
import R6_6_1EdgeB107
import R6_6_1EdgeB108
import R6_6_1EdgeB109
import R6_6_1EdgeB110
import R6_6_1EdgeB111
import R6_6_1EdgeB112
import R6_6_1EdgeB113
import R6_6_1EdgeB114
import R6_6_1EdgeB115
import R6_6_1EdgeB116
import R6_6_1EdgeB117
import R6_6_1EdgeB118
import R6_6_1EdgeB119
import R6_6_1EdgeB120
import R6_6_1EdgeB121
import R6_6_1EdgeB122
import R6_6_1EdgeB123
import R6_6_1EdgeB124
import R6_6_1EdgeB125
import R6_6_1EdgeB126
import R6_6_1EdgeB127
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem edge_check : ∀ m : Fin 4096, m.val ≠ 0 → ∀ vw ∈ edges,
  digit (table m.val) vw.1.val ≤ digit (table m.val) vw.2.val + 1 := by
  intro m
  by_cases h64 : m.val < 2048
  ·
    by_cases h32 : m.val < 1024
    ·
      by_cases h16 : m.val < 512
      ·
        by_cases h8 : m.val < 256
        ·
          by_cases h4 : m.val < 128
          ·
            by_cases h2 : m.val < 64
            ·
              by_cases h1 : m.val < 32
              ·
                have hb : m.val-0 < 32 := by omega
                have he : m.val-0+0 = m.val := by omega
                have hp := edge_checkB0 ⟨m.val-0,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-32 < 32 := by omega
                have he : m.val-32+32 = m.val := by omega
                have hp := edge_checkB1 ⟨m.val-32,hb⟩
                simpa only [he] using hp
            ·
              by_cases h3 : m.val < 96
              ·
                have hb : m.val-64 < 32 := by omega
                have he : m.val-64+64 = m.val := by omega
                have hp := edge_checkB2 ⟨m.val-64,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-96 < 32 := by omega
                have he : m.val-96+96 = m.val := by omega
                have hp := edge_checkB3 ⟨m.val-96,hb⟩
                simpa only [he] using hp
          ·
            by_cases h6 : m.val < 192
            ·
              by_cases h5 : m.val < 160
              ·
                have hb : m.val-128 < 32 := by omega
                have he : m.val-128+128 = m.val := by omega
                have hp := edge_checkB4 ⟨m.val-128,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-160 < 32 := by omega
                have he : m.val-160+160 = m.val := by omega
                have hp := edge_checkB5 ⟨m.val-160,hb⟩
                simpa only [he] using hp
            ·
              by_cases h7 : m.val < 224
              ·
                have hb : m.val-192 < 32 := by omega
                have he : m.val-192+192 = m.val := by omega
                have hp := edge_checkB6 ⟨m.val-192,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-224 < 32 := by omega
                have he : m.val-224+224 = m.val := by omega
                have hp := edge_checkB7 ⟨m.val-224,hb⟩
                simpa only [he] using hp
        ·
          by_cases h12 : m.val < 384
          ·
            by_cases h10 : m.val < 320
            ·
              by_cases h9 : m.val < 288
              ·
                have hb : m.val-256 < 32 := by omega
                have he : m.val-256+256 = m.val := by omega
                have hp := edge_checkB8 ⟨m.val-256,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-288 < 32 := by omega
                have he : m.val-288+288 = m.val := by omega
                have hp := edge_checkB9 ⟨m.val-288,hb⟩
                simpa only [he] using hp
            ·
              by_cases h11 : m.val < 352
              ·
                have hb : m.val-320 < 32 := by omega
                have he : m.val-320+320 = m.val := by omega
                have hp := edge_checkB10 ⟨m.val-320,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-352 < 32 := by omega
                have he : m.val-352+352 = m.val := by omega
                have hp := edge_checkB11 ⟨m.val-352,hb⟩
                simpa only [he] using hp
          ·
            by_cases h14 : m.val < 448
            ·
              by_cases h13 : m.val < 416
              ·
                have hb : m.val-384 < 32 := by omega
                have he : m.val-384+384 = m.val := by omega
                have hp := edge_checkB12 ⟨m.val-384,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-416 < 32 := by omega
                have he : m.val-416+416 = m.val := by omega
                have hp := edge_checkB13 ⟨m.val-416,hb⟩
                simpa only [he] using hp
            ·
              by_cases h15 : m.val < 480
              ·
                have hb : m.val-448 < 32 := by omega
                have he : m.val-448+448 = m.val := by omega
                have hp := edge_checkB14 ⟨m.val-448,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-480 < 32 := by omega
                have he : m.val-480+480 = m.val := by omega
                have hp := edge_checkB15 ⟨m.val-480,hb⟩
                simpa only [he] using hp
      ·
        by_cases h24 : m.val < 768
        ·
          by_cases h20 : m.val < 640
          ·
            by_cases h18 : m.val < 576
            ·
              by_cases h17 : m.val < 544
              ·
                have hb : m.val-512 < 32 := by omega
                have he : m.val-512+512 = m.val := by omega
                have hp := edge_checkB16 ⟨m.val-512,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-544 < 32 := by omega
                have he : m.val-544+544 = m.val := by omega
                have hp := edge_checkB17 ⟨m.val-544,hb⟩
                simpa only [he] using hp
            ·
              by_cases h19 : m.val < 608
              ·
                have hb : m.val-576 < 32 := by omega
                have he : m.val-576+576 = m.val := by omega
                have hp := edge_checkB18 ⟨m.val-576,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-608 < 32 := by omega
                have he : m.val-608+608 = m.val := by omega
                have hp := edge_checkB19 ⟨m.val-608,hb⟩
                simpa only [he] using hp
          ·
            by_cases h22 : m.val < 704
            ·
              by_cases h21 : m.val < 672
              ·
                have hb : m.val-640 < 32 := by omega
                have he : m.val-640+640 = m.val := by omega
                have hp := edge_checkB20 ⟨m.val-640,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-672 < 32 := by omega
                have he : m.val-672+672 = m.val := by omega
                have hp := edge_checkB21 ⟨m.val-672,hb⟩
                simpa only [he] using hp
            ·
              by_cases h23 : m.val < 736
              ·
                have hb : m.val-704 < 32 := by omega
                have he : m.val-704+704 = m.val := by omega
                have hp := edge_checkB22 ⟨m.val-704,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-736 < 32 := by omega
                have he : m.val-736+736 = m.val := by omega
                have hp := edge_checkB23 ⟨m.val-736,hb⟩
                simpa only [he] using hp
        ·
          by_cases h28 : m.val < 896
          ·
            by_cases h26 : m.val < 832
            ·
              by_cases h25 : m.val < 800
              ·
                have hb : m.val-768 < 32 := by omega
                have he : m.val-768+768 = m.val := by omega
                have hp := edge_checkB24 ⟨m.val-768,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-800 < 32 := by omega
                have he : m.val-800+800 = m.val := by omega
                have hp := edge_checkB25 ⟨m.val-800,hb⟩
                simpa only [he] using hp
            ·
              by_cases h27 : m.val < 864
              ·
                have hb : m.val-832 < 32 := by omega
                have he : m.val-832+832 = m.val := by omega
                have hp := edge_checkB26 ⟨m.val-832,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-864 < 32 := by omega
                have he : m.val-864+864 = m.val := by omega
                have hp := edge_checkB27 ⟨m.val-864,hb⟩
                simpa only [he] using hp
          ·
            by_cases h30 : m.val < 960
            ·
              by_cases h29 : m.val < 928
              ·
                have hb : m.val-896 < 32 := by omega
                have he : m.val-896+896 = m.val := by omega
                have hp := edge_checkB28 ⟨m.val-896,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-928 < 32 := by omega
                have he : m.val-928+928 = m.val := by omega
                have hp := edge_checkB29 ⟨m.val-928,hb⟩
                simpa only [he] using hp
            ·
              by_cases h31 : m.val < 992
              ·
                have hb : m.val-960 < 32 := by omega
                have he : m.val-960+960 = m.val := by omega
                have hp := edge_checkB30 ⟨m.val-960,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-992 < 32 := by omega
                have he : m.val-992+992 = m.val := by omega
                have hp := edge_checkB31 ⟨m.val-992,hb⟩
                simpa only [he] using hp
    ·
      by_cases h48 : m.val < 1536
      ·
        by_cases h40 : m.val < 1280
        ·
          by_cases h36 : m.val < 1152
          ·
            by_cases h34 : m.val < 1088
            ·
              by_cases h33 : m.val < 1056
              ·
                have hb : m.val-1024 < 32 := by omega
                have he : m.val-1024+1024 = m.val := by omega
                have hp := edge_checkB32 ⟨m.val-1024,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1056 < 32 := by omega
                have he : m.val-1056+1056 = m.val := by omega
                have hp := edge_checkB33 ⟨m.val-1056,hb⟩
                simpa only [he] using hp
            ·
              by_cases h35 : m.val < 1120
              ·
                have hb : m.val-1088 < 32 := by omega
                have he : m.val-1088+1088 = m.val := by omega
                have hp := edge_checkB34 ⟨m.val-1088,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1120 < 32 := by omega
                have he : m.val-1120+1120 = m.val := by omega
                have hp := edge_checkB35 ⟨m.val-1120,hb⟩
                simpa only [he] using hp
          ·
            by_cases h38 : m.val < 1216
            ·
              by_cases h37 : m.val < 1184
              ·
                have hb : m.val-1152 < 32 := by omega
                have he : m.val-1152+1152 = m.val := by omega
                have hp := edge_checkB36 ⟨m.val-1152,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1184 < 32 := by omega
                have he : m.val-1184+1184 = m.val := by omega
                have hp := edge_checkB37 ⟨m.val-1184,hb⟩
                simpa only [he] using hp
            ·
              by_cases h39 : m.val < 1248
              ·
                have hb : m.val-1216 < 32 := by omega
                have he : m.val-1216+1216 = m.val := by omega
                have hp := edge_checkB38 ⟨m.val-1216,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1248 < 32 := by omega
                have he : m.val-1248+1248 = m.val := by omega
                have hp := edge_checkB39 ⟨m.val-1248,hb⟩
                simpa only [he] using hp
        ·
          by_cases h44 : m.val < 1408
          ·
            by_cases h42 : m.val < 1344
            ·
              by_cases h41 : m.val < 1312
              ·
                have hb : m.val-1280 < 32 := by omega
                have he : m.val-1280+1280 = m.val := by omega
                have hp := edge_checkB40 ⟨m.val-1280,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1312 < 32 := by omega
                have he : m.val-1312+1312 = m.val := by omega
                have hp := edge_checkB41 ⟨m.val-1312,hb⟩
                simpa only [he] using hp
            ·
              by_cases h43 : m.val < 1376
              ·
                have hb : m.val-1344 < 32 := by omega
                have he : m.val-1344+1344 = m.val := by omega
                have hp := edge_checkB42 ⟨m.val-1344,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1376 < 32 := by omega
                have he : m.val-1376+1376 = m.val := by omega
                have hp := edge_checkB43 ⟨m.val-1376,hb⟩
                simpa only [he] using hp
          ·
            by_cases h46 : m.val < 1472
            ·
              by_cases h45 : m.val < 1440
              ·
                have hb : m.val-1408 < 32 := by omega
                have he : m.val-1408+1408 = m.val := by omega
                have hp := edge_checkB44 ⟨m.val-1408,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1440 < 32 := by omega
                have he : m.val-1440+1440 = m.val := by omega
                have hp := edge_checkB45 ⟨m.val-1440,hb⟩
                simpa only [he] using hp
            ·
              by_cases h47 : m.val < 1504
              ·
                have hb : m.val-1472 < 32 := by omega
                have he : m.val-1472+1472 = m.val := by omega
                have hp := edge_checkB46 ⟨m.val-1472,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1504 < 32 := by omega
                have he : m.val-1504+1504 = m.val := by omega
                have hp := edge_checkB47 ⟨m.val-1504,hb⟩
                simpa only [he] using hp
      ·
        by_cases h56 : m.val < 1792
        ·
          by_cases h52 : m.val < 1664
          ·
            by_cases h50 : m.val < 1600
            ·
              by_cases h49 : m.val < 1568
              ·
                have hb : m.val-1536 < 32 := by omega
                have he : m.val-1536+1536 = m.val := by omega
                have hp := edge_checkB48 ⟨m.val-1536,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1568 < 32 := by omega
                have he : m.val-1568+1568 = m.val := by omega
                have hp := edge_checkB49 ⟨m.val-1568,hb⟩
                simpa only [he] using hp
            ·
              by_cases h51 : m.val < 1632
              ·
                have hb : m.val-1600 < 32 := by omega
                have he : m.val-1600+1600 = m.val := by omega
                have hp := edge_checkB50 ⟨m.val-1600,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1632 < 32 := by omega
                have he : m.val-1632+1632 = m.val := by omega
                have hp := edge_checkB51 ⟨m.val-1632,hb⟩
                simpa only [he] using hp
          ·
            by_cases h54 : m.val < 1728
            ·
              by_cases h53 : m.val < 1696
              ·
                have hb : m.val-1664 < 32 := by omega
                have he : m.val-1664+1664 = m.val := by omega
                have hp := edge_checkB52 ⟨m.val-1664,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1696 < 32 := by omega
                have he : m.val-1696+1696 = m.val := by omega
                have hp := edge_checkB53 ⟨m.val-1696,hb⟩
                simpa only [he] using hp
            ·
              by_cases h55 : m.val < 1760
              ·
                have hb : m.val-1728 < 32 := by omega
                have he : m.val-1728+1728 = m.val := by omega
                have hp := edge_checkB54 ⟨m.val-1728,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1760 < 32 := by omega
                have he : m.val-1760+1760 = m.val := by omega
                have hp := edge_checkB55 ⟨m.val-1760,hb⟩
                simpa only [he] using hp
        ·
          by_cases h60 : m.val < 1920
          ·
            by_cases h58 : m.val < 1856
            ·
              by_cases h57 : m.val < 1824
              ·
                have hb : m.val-1792 < 32 := by omega
                have he : m.val-1792+1792 = m.val := by omega
                have hp := edge_checkB56 ⟨m.val-1792,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1824 < 32 := by omega
                have he : m.val-1824+1824 = m.val := by omega
                have hp := edge_checkB57 ⟨m.val-1824,hb⟩
                simpa only [he] using hp
            ·
              by_cases h59 : m.val < 1888
              ·
                have hb : m.val-1856 < 32 := by omega
                have he : m.val-1856+1856 = m.val := by omega
                have hp := edge_checkB58 ⟨m.val-1856,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1888 < 32 := by omega
                have he : m.val-1888+1888 = m.val := by omega
                have hp := edge_checkB59 ⟨m.val-1888,hb⟩
                simpa only [he] using hp
          ·
            by_cases h62 : m.val < 1984
            ·
              by_cases h61 : m.val < 1952
              ·
                have hb : m.val-1920 < 32 := by omega
                have he : m.val-1920+1920 = m.val := by omega
                have hp := edge_checkB60 ⟨m.val-1920,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-1952 < 32 := by omega
                have he : m.val-1952+1952 = m.val := by omega
                have hp := edge_checkB61 ⟨m.val-1952,hb⟩
                simpa only [he] using hp
            ·
              by_cases h63 : m.val < 2016
              ·
                have hb : m.val-1984 < 32 := by omega
                have he : m.val-1984+1984 = m.val := by omega
                have hp := edge_checkB62 ⟨m.val-1984,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2016 < 32 := by omega
                have he : m.val-2016+2016 = m.val := by omega
                have hp := edge_checkB63 ⟨m.val-2016,hb⟩
                simpa only [he] using hp
  ·
    by_cases h96 : m.val < 3072
    ·
      by_cases h80 : m.val < 2560
      ·
        by_cases h72 : m.val < 2304
        ·
          by_cases h68 : m.val < 2176
          ·
            by_cases h66 : m.val < 2112
            ·
              by_cases h65 : m.val < 2080
              ·
                have hb : m.val-2048 < 32 := by omega
                have he : m.val-2048+2048 = m.val := by omega
                have hp := edge_checkB64 ⟨m.val-2048,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2080 < 32 := by omega
                have he : m.val-2080+2080 = m.val := by omega
                have hp := edge_checkB65 ⟨m.val-2080,hb⟩
                simpa only [he] using hp
            ·
              by_cases h67 : m.val < 2144
              ·
                have hb : m.val-2112 < 32 := by omega
                have he : m.val-2112+2112 = m.val := by omega
                have hp := edge_checkB66 ⟨m.val-2112,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2144 < 32 := by omega
                have he : m.val-2144+2144 = m.val := by omega
                have hp := edge_checkB67 ⟨m.val-2144,hb⟩
                simpa only [he] using hp
          ·
            by_cases h70 : m.val < 2240
            ·
              by_cases h69 : m.val < 2208
              ·
                have hb : m.val-2176 < 32 := by omega
                have he : m.val-2176+2176 = m.val := by omega
                have hp := edge_checkB68 ⟨m.val-2176,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2208 < 32 := by omega
                have he : m.val-2208+2208 = m.val := by omega
                have hp := edge_checkB69 ⟨m.val-2208,hb⟩
                simpa only [he] using hp
            ·
              by_cases h71 : m.val < 2272
              ·
                have hb : m.val-2240 < 32 := by omega
                have he : m.val-2240+2240 = m.val := by omega
                have hp := edge_checkB70 ⟨m.val-2240,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2272 < 32 := by omega
                have he : m.val-2272+2272 = m.val := by omega
                have hp := edge_checkB71 ⟨m.val-2272,hb⟩
                simpa only [he] using hp
        ·
          by_cases h76 : m.val < 2432
          ·
            by_cases h74 : m.val < 2368
            ·
              by_cases h73 : m.val < 2336
              ·
                have hb : m.val-2304 < 32 := by omega
                have he : m.val-2304+2304 = m.val := by omega
                have hp := edge_checkB72 ⟨m.val-2304,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2336 < 32 := by omega
                have he : m.val-2336+2336 = m.val := by omega
                have hp := edge_checkB73 ⟨m.val-2336,hb⟩
                simpa only [he] using hp
            ·
              by_cases h75 : m.val < 2400
              ·
                have hb : m.val-2368 < 32 := by omega
                have he : m.val-2368+2368 = m.val := by omega
                have hp := edge_checkB74 ⟨m.val-2368,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2400 < 32 := by omega
                have he : m.val-2400+2400 = m.val := by omega
                have hp := edge_checkB75 ⟨m.val-2400,hb⟩
                simpa only [he] using hp
          ·
            by_cases h78 : m.val < 2496
            ·
              by_cases h77 : m.val < 2464
              ·
                have hb : m.val-2432 < 32 := by omega
                have he : m.val-2432+2432 = m.val := by omega
                have hp := edge_checkB76 ⟨m.val-2432,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2464 < 32 := by omega
                have he : m.val-2464+2464 = m.val := by omega
                have hp := edge_checkB77 ⟨m.val-2464,hb⟩
                simpa only [he] using hp
            ·
              by_cases h79 : m.val < 2528
              ·
                have hb : m.val-2496 < 32 := by omega
                have he : m.val-2496+2496 = m.val := by omega
                have hp := edge_checkB78 ⟨m.val-2496,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2528 < 32 := by omega
                have he : m.val-2528+2528 = m.val := by omega
                have hp := edge_checkB79 ⟨m.val-2528,hb⟩
                simpa only [he] using hp
      ·
        by_cases h88 : m.val < 2816
        ·
          by_cases h84 : m.val < 2688
          ·
            by_cases h82 : m.val < 2624
            ·
              by_cases h81 : m.val < 2592
              ·
                have hb : m.val-2560 < 32 := by omega
                have he : m.val-2560+2560 = m.val := by omega
                have hp := edge_checkB80 ⟨m.val-2560,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2592 < 32 := by omega
                have he : m.val-2592+2592 = m.val := by omega
                have hp := edge_checkB81 ⟨m.val-2592,hb⟩
                simpa only [he] using hp
            ·
              by_cases h83 : m.val < 2656
              ·
                have hb : m.val-2624 < 32 := by omega
                have he : m.val-2624+2624 = m.val := by omega
                have hp := edge_checkB82 ⟨m.val-2624,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2656 < 32 := by omega
                have he : m.val-2656+2656 = m.val := by omega
                have hp := edge_checkB83 ⟨m.val-2656,hb⟩
                simpa only [he] using hp
          ·
            by_cases h86 : m.val < 2752
            ·
              by_cases h85 : m.val < 2720
              ·
                have hb : m.val-2688 < 32 := by omega
                have he : m.val-2688+2688 = m.val := by omega
                have hp := edge_checkB84 ⟨m.val-2688,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2720 < 32 := by omega
                have he : m.val-2720+2720 = m.val := by omega
                have hp := edge_checkB85 ⟨m.val-2720,hb⟩
                simpa only [he] using hp
            ·
              by_cases h87 : m.val < 2784
              ·
                have hb : m.val-2752 < 32 := by omega
                have he : m.val-2752+2752 = m.val := by omega
                have hp := edge_checkB86 ⟨m.val-2752,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2784 < 32 := by omega
                have he : m.val-2784+2784 = m.val := by omega
                have hp := edge_checkB87 ⟨m.val-2784,hb⟩
                simpa only [he] using hp
        ·
          by_cases h92 : m.val < 2944
          ·
            by_cases h90 : m.val < 2880
            ·
              by_cases h89 : m.val < 2848
              ·
                have hb : m.val-2816 < 32 := by omega
                have he : m.val-2816+2816 = m.val := by omega
                have hp := edge_checkB88 ⟨m.val-2816,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2848 < 32 := by omega
                have he : m.val-2848+2848 = m.val := by omega
                have hp := edge_checkB89 ⟨m.val-2848,hb⟩
                simpa only [he] using hp
            ·
              by_cases h91 : m.val < 2912
              ·
                have hb : m.val-2880 < 32 := by omega
                have he : m.val-2880+2880 = m.val := by omega
                have hp := edge_checkB90 ⟨m.val-2880,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2912 < 32 := by omega
                have he : m.val-2912+2912 = m.val := by omega
                have hp := edge_checkB91 ⟨m.val-2912,hb⟩
                simpa only [he] using hp
          ·
            by_cases h94 : m.val < 3008
            ·
              by_cases h93 : m.val < 2976
              ·
                have hb : m.val-2944 < 32 := by omega
                have he : m.val-2944+2944 = m.val := by omega
                have hp := edge_checkB92 ⟨m.val-2944,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-2976 < 32 := by omega
                have he : m.val-2976+2976 = m.val := by omega
                have hp := edge_checkB93 ⟨m.val-2976,hb⟩
                simpa only [he] using hp
            ·
              by_cases h95 : m.val < 3040
              ·
                have hb : m.val-3008 < 32 := by omega
                have he : m.val-3008+3008 = m.val := by omega
                have hp := edge_checkB94 ⟨m.val-3008,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3040 < 32 := by omega
                have he : m.val-3040+3040 = m.val := by omega
                have hp := edge_checkB95 ⟨m.val-3040,hb⟩
                simpa only [he] using hp
    ·
      by_cases h112 : m.val < 3584
      ·
        by_cases h104 : m.val < 3328
        ·
          by_cases h100 : m.val < 3200
          ·
            by_cases h98 : m.val < 3136
            ·
              by_cases h97 : m.val < 3104
              ·
                have hb : m.val-3072 < 32 := by omega
                have he : m.val-3072+3072 = m.val := by omega
                have hp := edge_checkB96 ⟨m.val-3072,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3104 < 32 := by omega
                have he : m.val-3104+3104 = m.val := by omega
                have hp := edge_checkB97 ⟨m.val-3104,hb⟩
                simpa only [he] using hp
            ·
              by_cases h99 : m.val < 3168
              ·
                have hb : m.val-3136 < 32 := by omega
                have he : m.val-3136+3136 = m.val := by omega
                have hp := edge_checkB98 ⟨m.val-3136,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3168 < 32 := by omega
                have he : m.val-3168+3168 = m.val := by omega
                have hp := edge_checkB99 ⟨m.val-3168,hb⟩
                simpa only [he] using hp
          ·
            by_cases h102 : m.val < 3264
            ·
              by_cases h101 : m.val < 3232
              ·
                have hb : m.val-3200 < 32 := by omega
                have he : m.val-3200+3200 = m.val := by omega
                have hp := edge_checkB100 ⟨m.val-3200,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3232 < 32 := by omega
                have he : m.val-3232+3232 = m.val := by omega
                have hp := edge_checkB101 ⟨m.val-3232,hb⟩
                simpa only [he] using hp
            ·
              by_cases h103 : m.val < 3296
              ·
                have hb : m.val-3264 < 32 := by omega
                have he : m.val-3264+3264 = m.val := by omega
                have hp := edge_checkB102 ⟨m.val-3264,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3296 < 32 := by omega
                have he : m.val-3296+3296 = m.val := by omega
                have hp := edge_checkB103 ⟨m.val-3296,hb⟩
                simpa only [he] using hp
        ·
          by_cases h108 : m.val < 3456
          ·
            by_cases h106 : m.val < 3392
            ·
              by_cases h105 : m.val < 3360
              ·
                have hb : m.val-3328 < 32 := by omega
                have he : m.val-3328+3328 = m.val := by omega
                have hp := edge_checkB104 ⟨m.val-3328,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3360 < 32 := by omega
                have he : m.val-3360+3360 = m.val := by omega
                have hp := edge_checkB105 ⟨m.val-3360,hb⟩
                simpa only [he] using hp
            ·
              by_cases h107 : m.val < 3424
              ·
                have hb : m.val-3392 < 32 := by omega
                have he : m.val-3392+3392 = m.val := by omega
                have hp := edge_checkB106 ⟨m.val-3392,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3424 < 32 := by omega
                have he : m.val-3424+3424 = m.val := by omega
                have hp := edge_checkB107 ⟨m.val-3424,hb⟩
                simpa only [he] using hp
          ·
            by_cases h110 : m.val < 3520
            ·
              by_cases h109 : m.val < 3488
              ·
                have hb : m.val-3456 < 32 := by omega
                have he : m.val-3456+3456 = m.val := by omega
                have hp := edge_checkB108 ⟨m.val-3456,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3488 < 32 := by omega
                have he : m.val-3488+3488 = m.val := by omega
                have hp := edge_checkB109 ⟨m.val-3488,hb⟩
                simpa only [he] using hp
            ·
              by_cases h111 : m.val < 3552
              ·
                have hb : m.val-3520 < 32 := by omega
                have he : m.val-3520+3520 = m.val := by omega
                have hp := edge_checkB110 ⟨m.val-3520,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3552 < 32 := by omega
                have he : m.val-3552+3552 = m.val := by omega
                have hp := edge_checkB111 ⟨m.val-3552,hb⟩
                simpa only [he] using hp
      ·
        by_cases h120 : m.val < 3840
        ·
          by_cases h116 : m.val < 3712
          ·
            by_cases h114 : m.val < 3648
            ·
              by_cases h113 : m.val < 3616
              ·
                have hb : m.val-3584 < 32 := by omega
                have he : m.val-3584+3584 = m.val := by omega
                have hp := edge_checkB112 ⟨m.val-3584,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3616 < 32 := by omega
                have he : m.val-3616+3616 = m.val := by omega
                have hp := edge_checkB113 ⟨m.val-3616,hb⟩
                simpa only [he] using hp
            ·
              by_cases h115 : m.val < 3680
              ·
                have hb : m.val-3648 < 32 := by omega
                have he : m.val-3648+3648 = m.val := by omega
                have hp := edge_checkB114 ⟨m.val-3648,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3680 < 32 := by omega
                have he : m.val-3680+3680 = m.val := by omega
                have hp := edge_checkB115 ⟨m.val-3680,hb⟩
                simpa only [he] using hp
          ·
            by_cases h118 : m.val < 3776
            ·
              by_cases h117 : m.val < 3744
              ·
                have hb : m.val-3712 < 32 := by omega
                have he : m.val-3712+3712 = m.val := by omega
                have hp := edge_checkB116 ⟨m.val-3712,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3744 < 32 := by omega
                have he : m.val-3744+3744 = m.val := by omega
                have hp := edge_checkB117 ⟨m.val-3744,hb⟩
                simpa only [he] using hp
            ·
              by_cases h119 : m.val < 3808
              ·
                have hb : m.val-3776 < 32 := by omega
                have he : m.val-3776+3776 = m.val := by omega
                have hp := edge_checkB118 ⟨m.val-3776,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3808 < 32 := by omega
                have he : m.val-3808+3808 = m.val := by omega
                have hp := edge_checkB119 ⟨m.val-3808,hb⟩
                simpa only [he] using hp
        ·
          by_cases h124 : m.val < 3968
          ·
            by_cases h122 : m.val < 3904
            ·
              by_cases h121 : m.val < 3872
              ·
                have hb : m.val-3840 < 32 := by omega
                have he : m.val-3840+3840 = m.val := by omega
                have hp := edge_checkB120 ⟨m.val-3840,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3872 < 32 := by omega
                have he : m.val-3872+3872 = m.val := by omega
                have hp := edge_checkB121 ⟨m.val-3872,hb⟩
                simpa only [he] using hp
            ·
              by_cases h123 : m.val < 3936
              ·
                have hb : m.val-3904 < 32 := by omega
                have he : m.val-3904+3904 = m.val := by omega
                have hp := edge_checkB122 ⟨m.val-3904,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-3936 < 32 := by omega
                have he : m.val-3936+3936 = m.val := by omega
                have hp := edge_checkB123 ⟨m.val-3936,hb⟩
                simpa only [he] using hp
          ·
            by_cases h126 : m.val < 4032
            ·
              by_cases h125 : m.val < 4000
              ·
                have hb : m.val-3968 < 32 := by omega
                have he : m.val-3968+3968 = m.val := by omega
                have hp := edge_checkB124 ⟨m.val-3968,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-4000 < 32 := by omega
                have he : m.val-4000+4000 = m.val := by omega
                have hp := edge_checkB125 ⟨m.val-4000,hb⟩
                simpa only [he] using hp
            ·
              by_cases h127 : m.val < 4064
              ·
                have hb : m.val-4032 < 32 := by omega
                have he : m.val-4032+4032 = m.val := by omega
                have hp := edge_checkB126 ⟨m.val-4032,hb⟩
                simpa only [he] using hp
              ·
                have hb : m.val-4064 < 32 := by omega
                have he : m.val-4064+4064 = m.val := by omega
                have hp := edge_checkB127 ⟨m.val-4064,hb⟩
                simpa only [he] using hp
end R6_6_1
