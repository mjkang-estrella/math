import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem check3_3_6 : all2 (fun c m => !fastFits (first 3 6 c 3 m) || decide ((((6:V) = 1 ∧ c = 8) ∨ (6 = 8 ∧ c = 1)) ∧ ((3 = 2 ∧ m = 6) ∨ (3 = 6 ∧ m = 2)))) = true := by decide +kernel
theorem case3_3_6 (c m : V) (hf : Fits (first 3 6 c 3 m)) : (((6:V) = 1 ∧ c = 8) ∨ (6 = 8 ∧ c = 1)) ∧ ((3 = 2 ∧ m = 6) ∨ (3 = 6 ∧ m = 2)) := by
  have hh := all2_sound check3_3_6 c m
  have ht := (fastFits_iff _).mpr hf
  simpa only [ht, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hh
end ChainPrefix
