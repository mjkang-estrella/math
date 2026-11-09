import R9_6_0Base0
import R9_6_0Base1
import R9_6_0Base2
import R9_6_0Base3
import R9_6_0Base4
import R9_6_0Base5
import R9_6_0Base6
import R9_6_0Base7
import R9_6_0Base8
import R9_6_0Base9
import R9_6_0Base10
import R9_6_0Base11
import R9_6_0Base12
import R9_6_0Base13
import R9_6_0Base14
import R9_6_0Base15
import R9_6_0Base16
import R9_6_0Base17
import R9_6_0Base18
import R9_6_0Base19
import R9_6_0Base20
import R9_6_0Base21
import R9_6_0Base22
import R9_6_0Base23
import R9_6_0Base24
import R9_6_0Base25
import R9_6_0Base26
import R9_6_0Base27
import R9_6_0Base28
import R9_6_0Base29
import R9_6_0Base30
import R9_6_0Base31
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check : ∀ m : Fin 512, m.val ≠ 0 → ∀ v : Fin 35,
  (∀ i ∈ decode 9 m.val, point v ∈ group i) → digit (table m.val) v.val ≤ 1 := by
  intro m
  by_cases h16 : m.val < 256
  ·
    by_cases h8 : m.val < 128
    ·
      by_cases h4 : m.val < 64
      ·
        by_cases h2 : m.val < 32
        ·
          by_cases h1 : m.val < 16
          ·
            have hb : m.val-0 < 16 := by omega
            have he : m.val-0+0 = m.val := by omega
            have hp := base_check0 ⟨m.val-0,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-16 < 16 := by omega
            have he : m.val-16+16 = m.val := by omega
            have hp := base_check1 ⟨m.val-16,hb⟩
            simpa only [he] using hp
        ·
          by_cases h3 : m.val < 48
          ·
            have hb : m.val-32 < 16 := by omega
            have he : m.val-32+32 = m.val := by omega
            have hp := base_check2 ⟨m.val-32,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-48 < 16 := by omega
            have he : m.val-48+48 = m.val := by omega
            have hp := base_check3 ⟨m.val-48,hb⟩
            simpa only [he] using hp
      ·
        by_cases h6 : m.val < 96
        ·
          by_cases h5 : m.val < 80
          ·
            have hb : m.val-64 < 16 := by omega
            have he : m.val-64+64 = m.val := by omega
            have hp := base_check4 ⟨m.val-64,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-80 < 16 := by omega
            have he : m.val-80+80 = m.val := by omega
            have hp := base_check5 ⟨m.val-80,hb⟩
            simpa only [he] using hp
        ·
          by_cases h7 : m.val < 112
          ·
            have hb : m.val-96 < 16 := by omega
            have he : m.val-96+96 = m.val := by omega
            have hp := base_check6 ⟨m.val-96,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-112 < 16 := by omega
            have he : m.val-112+112 = m.val := by omega
            have hp := base_check7 ⟨m.val-112,hb⟩
            simpa only [he] using hp
    ·
      by_cases h12 : m.val < 192
      ·
        by_cases h10 : m.val < 160
        ·
          by_cases h9 : m.val < 144
          ·
            have hb : m.val-128 < 16 := by omega
            have he : m.val-128+128 = m.val := by omega
            have hp := base_check8 ⟨m.val-128,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-144 < 16 := by omega
            have he : m.val-144+144 = m.val := by omega
            have hp := base_check9 ⟨m.val-144,hb⟩
            simpa only [he] using hp
        ·
          by_cases h11 : m.val < 176
          ·
            have hb : m.val-160 < 16 := by omega
            have he : m.val-160+160 = m.val := by omega
            have hp := base_check10 ⟨m.val-160,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-176 < 16 := by omega
            have he : m.val-176+176 = m.val := by omega
            have hp := base_check11 ⟨m.val-176,hb⟩
            simpa only [he] using hp
      ·
        by_cases h14 : m.val < 224
        ·
          by_cases h13 : m.val < 208
          ·
            have hb : m.val-192 < 16 := by omega
            have he : m.val-192+192 = m.val := by omega
            have hp := base_check12 ⟨m.val-192,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-208 < 16 := by omega
            have he : m.val-208+208 = m.val := by omega
            have hp := base_check13 ⟨m.val-208,hb⟩
            simpa only [he] using hp
        ·
          by_cases h15 : m.val < 240
          ·
            have hb : m.val-224 < 16 := by omega
            have he : m.val-224+224 = m.val := by omega
            have hp := base_check14 ⟨m.val-224,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-240 < 16 := by omega
            have he : m.val-240+240 = m.val := by omega
            have hp := base_check15 ⟨m.val-240,hb⟩
            simpa only [he] using hp
  ·
    by_cases h24 : m.val < 384
    ·
      by_cases h20 : m.val < 320
      ·
        by_cases h18 : m.val < 288
        ·
          by_cases h17 : m.val < 272
          ·
            have hb : m.val-256 < 16 := by omega
            have he : m.val-256+256 = m.val := by omega
            have hp := base_check16 ⟨m.val-256,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-272 < 16 := by omega
            have he : m.val-272+272 = m.val := by omega
            have hp := base_check17 ⟨m.val-272,hb⟩
            simpa only [he] using hp
        ·
          by_cases h19 : m.val < 304
          ·
            have hb : m.val-288 < 16 := by omega
            have he : m.val-288+288 = m.val := by omega
            have hp := base_check18 ⟨m.val-288,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-304 < 16 := by omega
            have he : m.val-304+304 = m.val := by omega
            have hp := base_check19 ⟨m.val-304,hb⟩
            simpa only [he] using hp
      ·
        by_cases h22 : m.val < 352
        ·
          by_cases h21 : m.val < 336
          ·
            have hb : m.val-320 < 16 := by omega
            have he : m.val-320+320 = m.val := by omega
            have hp := base_check20 ⟨m.val-320,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-336 < 16 := by omega
            have he : m.val-336+336 = m.val := by omega
            have hp := base_check21 ⟨m.val-336,hb⟩
            simpa only [he] using hp
        ·
          by_cases h23 : m.val < 368
          ·
            have hb : m.val-352 < 16 := by omega
            have he : m.val-352+352 = m.val := by omega
            have hp := base_check22 ⟨m.val-352,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-368 < 16 := by omega
            have he : m.val-368+368 = m.val := by omega
            have hp := base_check23 ⟨m.val-368,hb⟩
            simpa only [he] using hp
    ·
      by_cases h28 : m.val < 448
      ·
        by_cases h26 : m.val < 416
        ·
          by_cases h25 : m.val < 400
          ·
            have hb : m.val-384 < 16 := by omega
            have he : m.val-384+384 = m.val := by omega
            have hp := base_check24 ⟨m.val-384,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-400 < 16 := by omega
            have he : m.val-400+400 = m.val := by omega
            have hp := base_check25 ⟨m.val-400,hb⟩
            simpa only [he] using hp
        ·
          by_cases h27 : m.val < 432
          ·
            have hb : m.val-416 < 16 := by omega
            have he : m.val-416+416 = m.val := by omega
            have hp := base_check26 ⟨m.val-416,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-432 < 16 := by omega
            have he : m.val-432+432 = m.val := by omega
            have hp := base_check27 ⟨m.val-432,hb⟩
            simpa only [he] using hp
      ·
        by_cases h30 : m.val < 480
        ·
          by_cases h29 : m.val < 464
          ·
            have hb : m.val-448 < 16 := by omega
            have he : m.val-448+448 = m.val := by omega
            have hp := base_check28 ⟨m.val-448,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-464 < 16 := by omega
            have he : m.val-464+464 = m.val := by omega
            have hp := base_check29 ⟨m.val-464,hb⟩
            simpa only [he] using hp
        ·
          by_cases h31 : m.val < 496
          ·
            have hb : m.val-480 < 16 := by omega
            have he : m.val-480+480 = m.val := by omega
            have hp := base_check30 ⟨m.val-480,hb⟩
            simpa only [he] using hp
          ·
            have hb : m.val-496 < 16 := by omega
            have he : m.val-496+496 = m.val := by omega
            have hp := base_check31 ⟨m.val-496,hb⟩
            simpa only [he] using hp

end R9_6_0
