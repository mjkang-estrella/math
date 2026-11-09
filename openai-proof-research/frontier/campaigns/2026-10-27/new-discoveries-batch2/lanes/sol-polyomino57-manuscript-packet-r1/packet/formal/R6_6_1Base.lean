import R6_6_1BaseB0
import R6_6_1BaseB1
import R6_6_1BaseB2
import R6_6_1BaseB3
import R6_6_1BaseB4
import R6_6_1BaseB5
import R6_6_1BaseB6
import R6_6_1BaseB7
import R6_6_1BaseB8
import R6_6_1BaseB9
import R6_6_1BaseB10
import R6_6_1BaseB11
import R6_6_1BaseB12
import R6_6_1BaseB13
import R6_6_1BaseB14
import R6_6_1BaseB15
import R6_6_1BaseB16
import R6_6_1BaseB17
import R6_6_1BaseB18
import R6_6_1BaseB19
import R6_6_1BaseB20
import R6_6_1BaseB21
import R6_6_1BaseB22
import R6_6_1BaseB23
import R6_6_1BaseB24
import R6_6_1BaseB25
import R6_6_1BaseB26
import R6_6_1BaseB27
import R6_6_1BaseB28
import R6_6_1BaseB29
import R6_6_1BaseB30
import R6_6_1BaseB31
import R6_6_1BaseB32
import R6_6_1BaseB33
import R6_6_1BaseB34
import R6_6_1BaseB35
import R6_6_1BaseB36
import R6_6_1BaseB37
import R6_6_1BaseB38
import R6_6_1BaseB39
import R6_6_1BaseB40
import R6_6_1BaseB41
import R6_6_1BaseB42
import R6_6_1BaseB43
import R6_6_1BaseB44
import R6_6_1BaseB45
import R6_6_1BaseB46
import R6_6_1BaseB47
import R6_6_1BaseB48
import R6_6_1BaseB49
import R6_6_1BaseB50
import R6_6_1BaseB51
import R6_6_1BaseB52
import R6_6_1BaseB53
import R6_6_1BaseB54
import R6_6_1BaseB55
import R6_6_1BaseB56
import R6_6_1BaseB57
import R6_6_1BaseB58
import R6_6_1BaseB59
import R6_6_1BaseB60
import R6_6_1BaseB61
import R6_6_1BaseB62
import R6_6_1BaseB63
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check : ∀ m : Fin 4096, m.val ≠ 0 → ∀ v : Fin 24,
  (∀ i ∈ decode 12 m.val, point v ∈ group i) → digit (table m.val) v.val ≤ 1 := by
  intro m
  by_cases h32 : m.val < 2048
  ·
    by_cases h16 : m.val < 1024
    ·
      by_cases h8 : m.val < 512
      ·
        by_cases h4 : m.val < 256
        ·
          by_cases h2 : m.val < 128
          ·
            by_cases h1 : m.val < 64
            ·
              have hb : m.val-0 < 64 := by omega
              have he : m.val-0+0 = m.val := by omega
              have hp := base_checkB0 ⟨m.val-0,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-64 < 64 := by omega
              have he : m.val-64+64 = m.val := by omega
              have hp := base_checkB1 ⟨m.val-64,hb⟩
              simpa only [he] using hp
          ·
            by_cases h3 : m.val < 192
            ·
              have hb : m.val-128 < 64 := by omega
              have he : m.val-128+128 = m.val := by omega
              have hp := base_checkB2 ⟨m.val-128,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-192 < 64 := by omega
              have he : m.val-192+192 = m.val := by omega
              have hp := base_checkB3 ⟨m.val-192,hb⟩
              simpa only [he] using hp
        ·
          by_cases h6 : m.val < 384
          ·
            by_cases h5 : m.val < 320
            ·
              have hb : m.val-256 < 64 := by omega
              have he : m.val-256+256 = m.val := by omega
              have hp := base_checkB4 ⟨m.val-256,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-320 < 64 := by omega
              have he : m.val-320+320 = m.val := by omega
              have hp := base_checkB5 ⟨m.val-320,hb⟩
              simpa only [he] using hp
          ·
            by_cases h7 : m.val < 448
            ·
              have hb : m.val-384 < 64 := by omega
              have he : m.val-384+384 = m.val := by omega
              have hp := base_checkB6 ⟨m.val-384,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-448 < 64 := by omega
              have he : m.val-448+448 = m.val := by omega
              have hp := base_checkB7 ⟨m.val-448,hb⟩
              simpa only [he] using hp
      ·
        by_cases h12 : m.val < 768
        ·
          by_cases h10 : m.val < 640
          ·
            by_cases h9 : m.val < 576
            ·
              have hb : m.val-512 < 64 := by omega
              have he : m.val-512+512 = m.val := by omega
              have hp := base_checkB8 ⟨m.val-512,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-576 < 64 := by omega
              have he : m.val-576+576 = m.val := by omega
              have hp := base_checkB9 ⟨m.val-576,hb⟩
              simpa only [he] using hp
          ·
            by_cases h11 : m.val < 704
            ·
              have hb : m.val-640 < 64 := by omega
              have he : m.val-640+640 = m.val := by omega
              have hp := base_checkB10 ⟨m.val-640,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-704 < 64 := by omega
              have he : m.val-704+704 = m.val := by omega
              have hp := base_checkB11 ⟨m.val-704,hb⟩
              simpa only [he] using hp
        ·
          by_cases h14 : m.val < 896
          ·
            by_cases h13 : m.val < 832
            ·
              have hb : m.val-768 < 64 := by omega
              have he : m.val-768+768 = m.val := by omega
              have hp := base_checkB12 ⟨m.val-768,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-832 < 64 := by omega
              have he : m.val-832+832 = m.val := by omega
              have hp := base_checkB13 ⟨m.val-832,hb⟩
              simpa only [he] using hp
          ·
            by_cases h15 : m.val < 960
            ·
              have hb : m.val-896 < 64 := by omega
              have he : m.val-896+896 = m.val := by omega
              have hp := base_checkB14 ⟨m.val-896,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-960 < 64 := by omega
              have he : m.val-960+960 = m.val := by omega
              have hp := base_checkB15 ⟨m.val-960,hb⟩
              simpa only [he] using hp
    ·
      by_cases h24 : m.val < 1536
      ·
        by_cases h20 : m.val < 1280
        ·
          by_cases h18 : m.val < 1152
          ·
            by_cases h17 : m.val < 1088
            ·
              have hb : m.val-1024 < 64 := by omega
              have he : m.val-1024+1024 = m.val := by omega
              have hp := base_checkB16 ⟨m.val-1024,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-1088 < 64 := by omega
              have he : m.val-1088+1088 = m.val := by omega
              have hp := base_checkB17 ⟨m.val-1088,hb⟩
              simpa only [he] using hp
          ·
            by_cases h19 : m.val < 1216
            ·
              have hb : m.val-1152 < 64 := by omega
              have he : m.val-1152+1152 = m.val := by omega
              have hp := base_checkB18 ⟨m.val-1152,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-1216 < 64 := by omega
              have he : m.val-1216+1216 = m.val := by omega
              have hp := base_checkB19 ⟨m.val-1216,hb⟩
              simpa only [he] using hp
        ·
          by_cases h22 : m.val < 1408
          ·
            by_cases h21 : m.val < 1344
            ·
              have hb : m.val-1280 < 64 := by omega
              have he : m.val-1280+1280 = m.val := by omega
              have hp := base_checkB20 ⟨m.val-1280,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-1344 < 64 := by omega
              have he : m.val-1344+1344 = m.val := by omega
              have hp := base_checkB21 ⟨m.val-1344,hb⟩
              simpa only [he] using hp
          ·
            by_cases h23 : m.val < 1472
            ·
              have hb : m.val-1408 < 64 := by omega
              have he : m.val-1408+1408 = m.val := by omega
              have hp := base_checkB22 ⟨m.val-1408,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-1472 < 64 := by omega
              have he : m.val-1472+1472 = m.val := by omega
              have hp := base_checkB23 ⟨m.val-1472,hb⟩
              simpa only [he] using hp
      ·
        by_cases h28 : m.val < 1792
        ·
          by_cases h26 : m.val < 1664
          ·
            by_cases h25 : m.val < 1600
            ·
              have hb : m.val-1536 < 64 := by omega
              have he : m.val-1536+1536 = m.val := by omega
              have hp := base_checkB24 ⟨m.val-1536,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-1600 < 64 := by omega
              have he : m.val-1600+1600 = m.val := by omega
              have hp := base_checkB25 ⟨m.val-1600,hb⟩
              simpa only [he] using hp
          ·
            by_cases h27 : m.val < 1728
            ·
              have hb : m.val-1664 < 64 := by omega
              have he : m.val-1664+1664 = m.val := by omega
              have hp := base_checkB26 ⟨m.val-1664,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-1728 < 64 := by omega
              have he : m.val-1728+1728 = m.val := by omega
              have hp := base_checkB27 ⟨m.val-1728,hb⟩
              simpa only [he] using hp
        ·
          by_cases h30 : m.val < 1920
          ·
            by_cases h29 : m.val < 1856
            ·
              have hb : m.val-1792 < 64 := by omega
              have he : m.val-1792+1792 = m.val := by omega
              have hp := base_checkB28 ⟨m.val-1792,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-1856 < 64 := by omega
              have he : m.val-1856+1856 = m.val := by omega
              have hp := base_checkB29 ⟨m.val-1856,hb⟩
              simpa only [he] using hp
          ·
            by_cases h31 : m.val < 1984
            ·
              have hb : m.val-1920 < 64 := by omega
              have he : m.val-1920+1920 = m.val := by omega
              have hp := base_checkB30 ⟨m.val-1920,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-1984 < 64 := by omega
              have he : m.val-1984+1984 = m.val := by omega
              have hp := base_checkB31 ⟨m.val-1984,hb⟩
              simpa only [he] using hp
  ·
    by_cases h48 : m.val < 3072
    ·
      by_cases h40 : m.val < 2560
      ·
        by_cases h36 : m.val < 2304
        ·
          by_cases h34 : m.val < 2176
          ·
            by_cases h33 : m.val < 2112
            ·
              have hb : m.val-2048 < 64 := by omega
              have he : m.val-2048+2048 = m.val := by omega
              have hp := base_checkB32 ⟨m.val-2048,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-2112 < 64 := by omega
              have he : m.val-2112+2112 = m.val := by omega
              have hp := base_checkB33 ⟨m.val-2112,hb⟩
              simpa only [he] using hp
          ·
            by_cases h35 : m.val < 2240
            ·
              have hb : m.val-2176 < 64 := by omega
              have he : m.val-2176+2176 = m.val := by omega
              have hp := base_checkB34 ⟨m.val-2176,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-2240 < 64 := by omega
              have he : m.val-2240+2240 = m.val := by omega
              have hp := base_checkB35 ⟨m.val-2240,hb⟩
              simpa only [he] using hp
        ·
          by_cases h38 : m.val < 2432
          ·
            by_cases h37 : m.val < 2368
            ·
              have hb : m.val-2304 < 64 := by omega
              have he : m.val-2304+2304 = m.val := by omega
              have hp := base_checkB36 ⟨m.val-2304,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-2368 < 64 := by omega
              have he : m.val-2368+2368 = m.val := by omega
              have hp := base_checkB37 ⟨m.val-2368,hb⟩
              simpa only [he] using hp
          ·
            by_cases h39 : m.val < 2496
            ·
              have hb : m.val-2432 < 64 := by omega
              have he : m.val-2432+2432 = m.val := by omega
              have hp := base_checkB38 ⟨m.val-2432,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-2496 < 64 := by omega
              have he : m.val-2496+2496 = m.val := by omega
              have hp := base_checkB39 ⟨m.val-2496,hb⟩
              simpa only [he] using hp
      ·
        by_cases h44 : m.val < 2816
        ·
          by_cases h42 : m.val < 2688
          ·
            by_cases h41 : m.val < 2624
            ·
              have hb : m.val-2560 < 64 := by omega
              have he : m.val-2560+2560 = m.val := by omega
              have hp := base_checkB40 ⟨m.val-2560,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-2624 < 64 := by omega
              have he : m.val-2624+2624 = m.val := by omega
              have hp := base_checkB41 ⟨m.val-2624,hb⟩
              simpa only [he] using hp
          ·
            by_cases h43 : m.val < 2752
            ·
              have hb : m.val-2688 < 64 := by omega
              have he : m.val-2688+2688 = m.val := by omega
              have hp := base_checkB42 ⟨m.val-2688,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-2752 < 64 := by omega
              have he : m.val-2752+2752 = m.val := by omega
              have hp := base_checkB43 ⟨m.val-2752,hb⟩
              simpa only [he] using hp
        ·
          by_cases h46 : m.val < 2944
          ·
            by_cases h45 : m.val < 2880
            ·
              have hb : m.val-2816 < 64 := by omega
              have he : m.val-2816+2816 = m.val := by omega
              have hp := base_checkB44 ⟨m.val-2816,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-2880 < 64 := by omega
              have he : m.val-2880+2880 = m.val := by omega
              have hp := base_checkB45 ⟨m.val-2880,hb⟩
              simpa only [he] using hp
          ·
            by_cases h47 : m.val < 3008
            ·
              have hb : m.val-2944 < 64 := by omega
              have he : m.val-2944+2944 = m.val := by omega
              have hp := base_checkB46 ⟨m.val-2944,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-3008 < 64 := by omega
              have he : m.val-3008+3008 = m.val := by omega
              have hp := base_checkB47 ⟨m.val-3008,hb⟩
              simpa only [he] using hp
    ·
      by_cases h56 : m.val < 3584
      ·
        by_cases h52 : m.val < 3328
        ·
          by_cases h50 : m.val < 3200
          ·
            by_cases h49 : m.val < 3136
            ·
              have hb : m.val-3072 < 64 := by omega
              have he : m.val-3072+3072 = m.val := by omega
              have hp := base_checkB48 ⟨m.val-3072,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-3136 < 64 := by omega
              have he : m.val-3136+3136 = m.val := by omega
              have hp := base_checkB49 ⟨m.val-3136,hb⟩
              simpa only [he] using hp
          ·
            by_cases h51 : m.val < 3264
            ·
              have hb : m.val-3200 < 64 := by omega
              have he : m.val-3200+3200 = m.val := by omega
              have hp := base_checkB50 ⟨m.val-3200,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-3264 < 64 := by omega
              have he : m.val-3264+3264 = m.val := by omega
              have hp := base_checkB51 ⟨m.val-3264,hb⟩
              simpa only [he] using hp
        ·
          by_cases h54 : m.val < 3456
          ·
            by_cases h53 : m.val < 3392
            ·
              have hb : m.val-3328 < 64 := by omega
              have he : m.val-3328+3328 = m.val := by omega
              have hp := base_checkB52 ⟨m.val-3328,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-3392 < 64 := by omega
              have he : m.val-3392+3392 = m.val := by omega
              have hp := base_checkB53 ⟨m.val-3392,hb⟩
              simpa only [he] using hp
          ·
            by_cases h55 : m.val < 3520
            ·
              have hb : m.val-3456 < 64 := by omega
              have he : m.val-3456+3456 = m.val := by omega
              have hp := base_checkB54 ⟨m.val-3456,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-3520 < 64 := by omega
              have he : m.val-3520+3520 = m.val := by omega
              have hp := base_checkB55 ⟨m.val-3520,hb⟩
              simpa only [he] using hp
      ·
        by_cases h60 : m.val < 3840
        ·
          by_cases h58 : m.val < 3712
          ·
            by_cases h57 : m.val < 3648
            ·
              have hb : m.val-3584 < 64 := by omega
              have he : m.val-3584+3584 = m.val := by omega
              have hp := base_checkB56 ⟨m.val-3584,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-3648 < 64 := by omega
              have he : m.val-3648+3648 = m.val := by omega
              have hp := base_checkB57 ⟨m.val-3648,hb⟩
              simpa only [he] using hp
          ·
            by_cases h59 : m.val < 3776
            ·
              have hb : m.val-3712 < 64 := by omega
              have he : m.val-3712+3712 = m.val := by omega
              have hp := base_checkB58 ⟨m.val-3712,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-3776 < 64 := by omega
              have he : m.val-3776+3776 = m.val := by omega
              have hp := base_checkB59 ⟨m.val-3776,hb⟩
              simpa only [he] using hp
        ·
          by_cases h62 : m.val < 3968
          ·
            by_cases h61 : m.val < 3904
            ·
              have hb : m.val-3840 < 64 := by omega
              have he : m.val-3840+3840 = m.val := by omega
              have hp := base_checkB60 ⟨m.val-3840,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-3904 < 64 := by omega
              have he : m.val-3904+3904 = m.val := by omega
              have hp := base_checkB61 ⟨m.val-3904,hb⟩
              simpa only [he] using hp
          ·
            by_cases h63 : m.val < 4032
            ·
              have hb : m.val-3968 < 64 := by omega
              have he : m.val-3968+3968 = m.val := by omega
              have hp := base_checkB62 ⟨m.val-3968,hb⟩
              simpa only [he] using hp
            ·
              have hb : m.val-4032 < 64 := by omega
              have he : m.val-4032+4032 = m.val := by omega
              have hp := base_checkB63 ⟨m.val-4032,hb⟩
              simpa only [he] using hp
end R6_6_1
