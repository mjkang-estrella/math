import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem checkTail6_8_3_5 : all2 (fun t d => decide ((5:V) = 6 ∨ 5 = 8) ||
    !fastFits (first 6 8 1 3 4 ++ dbl 8 1 ++ tri 8 5 t ++ dbl 5 d)) = true := by decide +kernel
theorem tail6_8_3_5 (t d : V) (ha : (5:V) ≠ 6) (hb : (5:V) ≠ 8) :
    ¬Fits (first 6 8 1 3 4 ++ dbl 8 1 ++ tri 8 5 t ++ dbl 5 d) := by
  intro hf
  have ht := (fastFits_iff _).mpr hf
  have hh := all2_sound checkTail6_8_3_5 t d
  simp only [ha, hb, or_self, decide_false, Bool.false_or, ht, Bool.not_true, Bool.false_eq_true] at hh
end ChainPrefix
