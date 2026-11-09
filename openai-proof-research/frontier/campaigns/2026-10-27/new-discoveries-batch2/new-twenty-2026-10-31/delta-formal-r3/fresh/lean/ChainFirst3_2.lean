import ChainLocal
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem checkFirst3_2 : all2 (fun b c => !fastFits (first 3 b c 2 6) ||
    decide ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1))) = true := by decide +kernel
theorem first3_2 (b c : V) (hf : Fits (first 3 b c 2 6)) :
    (b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1) := by
  have hh := all2_sound checkFirst3_2 b c
  have ht := (fastFits_iff _).mpr hf
  simpa only [ht, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hh
end ChainPrefix
