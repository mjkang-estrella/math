import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem checkTail6_1_4_6 : all2 (fun t d => decide ((6:V) = 6 ∨ 6 = 1) ||
    !fastFits (first 6 1 8 4 3 ++ dbl 1 8 ++ tri 1 6 t ++ dbl 6 d)) = true := by decide +kernel
theorem tail6_1_4_6 (t d : V) (ha : (6:V) ≠ 6) (hb : (6:V) ≠ 1) :
    ¬Fits (first 6 1 8 4 3 ++ dbl 1 8 ++ tri 1 6 t ++ dbl 6 d) := by
  intro hf
  have ht := (fastFits_iff _).mpr hf
  have hh := all2_sound checkTail6_1_4_6 t d
  simp only [ha, hb, or_self, decide_false, Bool.false_or, ht, Bool.not_true, Bool.false_eq_true] at hh
end ChainPrefix
