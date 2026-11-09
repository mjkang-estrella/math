import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem checkTail6_8_4_3 : all2 (fun t d => decide ((3:V) = 6 ∨ 3 = 8) ||
    !fastFits (first 6 8 1 4 3 ++ dbl 8 1 ++ tri 8 3 t ++ dbl 3 d)) = true := by decide +kernel
theorem tail6_8_4_3 (t d : V) (ha : (3:V) ≠ 6) (hb : (3:V) ≠ 8) :
    ¬Fits (first 6 8 1 4 3 ++ dbl 8 1 ++ tri 8 3 t ++ dbl 3 d) := by
  intro hf
  have ht := (fastFits_iff _).mpr hf
  have hh := all2_sound checkTail6_8_4_3 t d
  simp only [ha, hb, or_self, decide_false, Bool.false_or, ht, Bool.not_true, Bool.false_eq_true] at hh
end ChainPrefix
