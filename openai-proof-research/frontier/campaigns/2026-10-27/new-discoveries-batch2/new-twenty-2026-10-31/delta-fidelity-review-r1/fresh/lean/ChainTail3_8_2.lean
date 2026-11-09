import ChainBool
namespace ChainPrefix
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem attach3_8_2 : ∀ d : V, Fits (first 3 8 1 2 6 ++ dbl 8 d) → d = 1 := by decide +kernel
theorem nextCheck3_8_2 : all2 (fun v t => decide (v = 3 ∨ v = 8) ||
  !fastFits (first 3 8 1 2 6 ++ dbl 8 1 ++ tri 8 v t) || decide (v = 4 ∨ v = 6)) = true := by decide +kernel
theorem block8_2_4 : all2 (fun t d => !fastFits (first 3 8 1 2 6 ++ dbl 8 1 ++ tri 8 4 t ++ dbl 4 d)) = true := by decide +kernel
theorem block8_2_6 : all2 (fun t d => !fastFits (first 3 8 1 2 6 ++ dbl 8 1 ++ tri 8 6 t ++ dbl 6 d)) = true := by decide +kernel
theorem tail3_8_2 (v t d : V) (ha : v ≠ 3) (hb : v ≠ 8) :
    ¬Fits (first 3 8 1 2 6 ++ dbl 8 1 ++ tri 8 v t ++ dbl v d) := by
  intro hf
  have hp : Fits (first 3 8 1 2 6 ++ dbl 8 1 ++ tri 8 v t) := by
    intro i j
    have hh := hf i j
    simp only [pairCount_append] at hh ⊢
    omega
  have hc := all2_sound nextCheck3_8_2 v t
  have ht := (fastFits_iff _).mpr hp
  simp only [ha, hb, or_self, decide_false, Bool.false_or, ht, Bool.not_true, Bool.false_eq_true, decide_eq_true_eq] at hc
  rcases hc with rfl | rfl
  · have hh := all2_sound block8_2_4 t d
    rw [(fastFits_iff _).mpr hf] at hh
    contradiction
  · have hh := all2_sound block8_2_6 t d
    rw [(fastFits_iff _).mpr hf] at hh
    contradiction
end ChainPrefix
