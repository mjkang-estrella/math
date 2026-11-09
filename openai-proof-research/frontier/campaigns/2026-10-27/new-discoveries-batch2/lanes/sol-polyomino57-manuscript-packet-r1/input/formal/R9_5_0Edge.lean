import R9_5_0EdgeB0
import R9_5_0EdgeB1
import R9_5_0EdgeB2
import R9_5_0EdgeB3
import R9_5_0EdgeB4
import R9_5_0EdgeB5
import R9_5_0EdgeB6
import R9_5_0EdgeB7
import R9_5_0EdgeB8
import R9_5_0EdgeB9
import R9_5_0EdgeB10
import R9_5_0EdgeB11
import R9_5_0EdgeB12
import R9_5_0EdgeB13
import R9_5_0EdgeB14
import R9_5_0EdgeB15
import R9_5_0EdgeB16
import R9_5_0EdgeB17
import R9_5_0EdgeB18
import R9_5_0EdgeB19
import R9_5_0EdgeB20
import R9_5_0EdgeB21
import R9_5_0EdgeB22
import R9_5_0EdgeB23
import R9_5_0EdgeB24
import R9_5_0EdgeB25
import R9_5_0EdgeB26
import R9_5_0EdgeB27
import R9_5_0EdgeB28
import R9_5_0EdgeB29
import R9_5_0EdgeB30
import R9_5_0EdgeB31
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem edge_check : ∀ m : Fin 1024, m.val ≠ 0 → ∀ vw ∈ edges,
  digit (table m.val) vw.1.val ≤ digit (table m.val) vw.2.val + 1 := by
  intro m
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
end R9_5_0
