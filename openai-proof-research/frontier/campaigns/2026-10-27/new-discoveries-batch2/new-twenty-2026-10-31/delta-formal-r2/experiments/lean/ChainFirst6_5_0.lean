import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem check6_5_0 : all2 (fun c m => !fastFits (first 6 0 c 5 m) || decide ((((0:V) = 1 ∧ c = 8) ∨ (0 = 8 ∧ c = 1)) ∧ ((5 = 3 ∧ m = 4) ∨ (5 = 4 ∧ m = 3)))) = true := by decide +kernel
theorem case6_5_0 (c m : V) (hf : Fits (first 6 0 c 5 m)) : (((0:V) = 1 ∧ c = 8) ∨ (0 = 8 ∧ c = 1)) ∧ ((5 = 3 ∧ m = 4) ∨ (5 = 4 ∧ m = 3)) := by
  have hh := all2_sound check6_5_0 c m
  have ht := (fastFits_iff _).mpr hf
  simpa only [ht, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hh
end ChainPrefix
