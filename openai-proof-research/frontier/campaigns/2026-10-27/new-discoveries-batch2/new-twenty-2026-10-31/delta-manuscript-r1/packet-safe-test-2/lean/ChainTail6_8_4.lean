import ChainBool
namespace ChainPrefix
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem attach6_8_4 : ∀ d : V, Fits (first 6 8 1 4 3 ++ dbl 8 d) → d = 1 := by decide +kernel
theorem nextCheck6_8_4 : all2 (fun v t => decide (v = 6 ∨ v = 8) ||
  !fastFits (first 6 8 1 4 3 ++ dbl 8 1 ++ tri 8 v t) || decide (False)) = true := by decide +kernel
theorem tail6_8_4 (v t d : V) (ha : v ≠ 6) (hb : v ≠ 8) :
    ¬Fits (first 6 8 1 4 3 ++ dbl 8 1 ++ tri 8 v t ++ dbl v d) := by
  intro hf
  have hp : Fits (first 6 8 1 4 3 ++ dbl 8 1 ++ tri 8 v t) := by
    intro i j
    have hh := hf i j
    simp only [pairCount_append] at hh ⊢
    omega
  have hc := all2_sound nextCheck6_8_4 v t
  have ht := (fastFits_iff _).mpr hp
  simp only [ha, hb, or_self, decide_false, Bool.false_or, ht, Bool.not_true, Bool.false_eq_true, decide_eq_true_eq] at hc
end ChainPrefix
