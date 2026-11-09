import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem check3_8_0 : all2 (fun c m => !fastFits (first 3 0 c 8 m) || decide ((((0:V) = 1 ∧ c = 8) ∨ (0 = 8 ∧ c = 1)) ∧ ((8 = 2 ∧ m = 6) ∨ (8 = 6 ∧ m = 2)))) = true := by decide +kernel
theorem case3_8_0 (c m : V) (hf : Fits (first 3 0 c 8 m)) : (((0:V) = 1 ∧ c = 8) ∨ (0 = 8 ∧ c = 1)) ∧ ((8 = 2 ∧ m = 6) ∨ (8 = 6 ∧ m = 2)) := by
  have hh := all2_sound check3_8_0 c m
  have ht := (fastFits_iff _).mpr hf
  simpa only [ht, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hh
end ChainPrefix
