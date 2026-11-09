import ChainBool
namespace ChainPrefix
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem attach6_1_3 : ∀ d : V, Fits (first 6 1 8 3 4 ++ dbl 1 d) → d = 8 := by decide +kernel
theorem nextCheck6_1_3 : all2 (fun v t => decide (v = 6 ∨ v = 1) ||
  !fastFits (first 6 1 8 3 4 ++ dbl 1 8 ++ tri 1 v t) || decide (False)) = true := by decide +kernel
theorem tail6_1_3 (v t d : V) (ha : v ≠ 6) (hb : v ≠ 1) :
    ¬Fits (first 6 1 8 3 4 ++ dbl 1 8 ++ tri 1 v t ++ dbl v d) := by
  intro hf
  have hp : Fits (first 6 1 8 3 4 ++ dbl 1 8 ++ tri 1 v t) := by
    intro i j
    have hh := hf i j
    simp only [pairCount_append] at hh ⊢
    omega
  have hc := all2_sound nextCheck6_1_3 v t
  have ht := (fastFits_iff _).mpr hp
  simp only [ha, hb, or_self, decide_false, Bool.false_or, ht, Bool.not_true, Bool.false_eq_true, decide_eq_true_eq] at hc
end ChainPrefix
