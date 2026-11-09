import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem checkTail3_1_6_7 : all2 (fun t d => decide ((7:V) = 3 ∨ 7 = 1) ||
    !fastFits (first 3 1 8 6 2 ++ dbl 1 8 ++ tri 1 7 t ++ dbl 7 d)) = true := by decide +kernel
theorem tail3_1_6_7 (t d : V) (ha : (7:V) ≠ 3) (hb : (7:V) ≠ 1) :
    ¬Fits (first 3 1 8 6 2 ++ dbl 1 8 ++ tri 1 7 t ++ dbl 7 d) := by
  intro hf
  have ht := (fastFits_iff _).mpr hf
  have hh := all2_sound checkTail3_1_6_7 t d
  simp only [ha, hb, or_self, decide_false, Bool.false_or, ht, Bool.not_true, Bool.false_eq_true] at hh
end ChainPrefix
