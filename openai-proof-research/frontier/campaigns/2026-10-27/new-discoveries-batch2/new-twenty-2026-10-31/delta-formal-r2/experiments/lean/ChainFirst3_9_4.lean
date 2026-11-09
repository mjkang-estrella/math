import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem check3_9_4 : all2 (fun c m => !fastFits (first 3 4 c 9 m) || decide ((((4:V) = 1 ∧ c = 8) ∨ (4 = 8 ∧ c = 1)) ∧ ((9 = 2 ∧ m = 6) ∨ (9 = 6 ∧ m = 2)))) = true := by decide +kernel
theorem case3_9_4 (c m : V) (hf : Fits (first 3 4 c 9 m)) : (((4:V) = 1 ∧ c = 8) ∨ (4 = 8 ∧ c = 1)) ∧ ((9 = 2 ∧ m = 6) ∨ (9 = 6 ∧ m = 2)) := by
  have hh := all2_sound check3_9_4 c m
  have ht := (fastFits_iff _).mpr hf
  simpa only [ht, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hh
end ChainPrefix
