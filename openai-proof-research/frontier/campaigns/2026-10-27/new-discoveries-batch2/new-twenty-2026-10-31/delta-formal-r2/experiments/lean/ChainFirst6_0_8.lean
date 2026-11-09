import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem check6_0_8 : all2 (fun c m => !fastFits (first 6 8 c 0 m) || decide ((((8:V) = 1 ∧ c = 8) ∨ (8 = 8 ∧ c = 1)) ∧ ((0 = 3 ∧ m = 4) ∨ (0 = 4 ∧ m = 3)))) = true := by decide +kernel
theorem case6_0_8 (c m : V) (hf : Fits (first 6 8 c 0 m)) : (((8:V) = 1 ∧ c = 8) ∨ (8 = 8 ∧ c = 1)) ∧ ((0 = 3 ∧ m = 4) ∨ (0 = 4 ∧ m = 3)) := by
  have hh := all2_sound check6_0_8 c m
  have ht := (fastFits_iff _).mpr hf
  simpa only [ht, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hh
end ChainPrefix
