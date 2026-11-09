import ChainLocal
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem checkFirst6_4 : all2 (fun b c => !fastFits (first 6 b c 4 3) ||
    decide ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1))) = true := by decide +kernel
theorem first6_4 (b c : V) (hf : Fits (first 6 b c 4 3)) :
    (b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1) := by
  have hh := all2_sound checkFirst6_4 b c
  have ht := (fastFits_iff _).mpr hf
  simpa only [ht, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hh
end ChainPrefix
