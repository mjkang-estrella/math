import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem checkTail6_1_3_10 : all2 (fun t d => decide ((10:V) = 6 ∨ 10 = 1) ||
    !fastFits (first 6 1 8 3 4 ++ dbl 1 8 ++ tri 1 10 t ++ dbl 10 d)) = true := by decide +kernel
theorem tail6_1_3_10 (t d : V) (ha : (10:V) ≠ 6) (hb : (10:V) ≠ 1) :
    ¬Fits (first 6 1 8 3 4 ++ dbl 1 8 ++ tri 1 10 t ++ dbl 10 d) := by
  intro hf
  have ht := (fastFits_iff _).mpr hf
  have hh := all2_sound checkTail6_1_3_10 t d
  simp only [ha, hb, or_self, decide_false, Bool.false_or, ht, Bool.not_true, Bool.false_eq_true] at hh
end ChainPrefix
