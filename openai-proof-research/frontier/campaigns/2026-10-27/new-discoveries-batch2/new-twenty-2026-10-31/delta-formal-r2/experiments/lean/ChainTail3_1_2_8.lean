import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem checkTail3_1_2_8 : all2 (fun t d => decide ((8:V) = 3 ∨ 8 = 1) ||
    !fastFits (first 3 1 8 2 6 ++ dbl 1 8 ++ tri 1 8 t ++ dbl 8 d)) = true := by decide +kernel
theorem tail3_1_2_8 (t d : V) (ha : (8:V) ≠ 3) (hb : (8:V) ≠ 1) :
    ¬Fits (first 3 1 8 2 6 ++ dbl 1 8 ++ tri 1 8 t ++ dbl 8 d) := by
  intro hf
  have ht := (fastFits_iff _).mpr hf
  have hh := all2_sound checkTail3_1_2_8 t d
  simp only [ha, hb, or_self, decide_false, Bool.false_or, ht, Bool.not_true, Bool.false_eq_true] at hh
end ChainPrefix
