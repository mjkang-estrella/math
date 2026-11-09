import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem checkTail6_8_4_10 : all2 (fun t d => decide ((10:V) = 6 ∨ 10 = 8) ||
    !fastFits (first 6 8 1 4 3 ++ dbl 8 1 ++ tri 8 10 t ++ dbl 10 d)) = true := by decide +kernel
theorem tail6_8_4_10 (t d : V) (ha : (10:V) ≠ 6) (hb : (10:V) ≠ 8) :
    ¬Fits (first 6 8 1 4 3 ++ dbl 8 1 ++ tri 8 10 t ++ dbl 10 d) := by
  intro hf
  have ht := (fastFits_iff _).mpr hf
  have hh := all2_sound checkTail6_8_4_10 t d
  simp only [ha, hb, or_self, decide_false, Bool.false_or, ht, Bool.not_true, Bool.false_eq_true] at hh
end ChainPrefix
