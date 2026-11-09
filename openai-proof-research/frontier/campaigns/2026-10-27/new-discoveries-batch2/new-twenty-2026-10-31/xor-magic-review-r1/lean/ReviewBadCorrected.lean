import BaseEndpoints
-- Must FAIL: CorrectedAt 4 cannot be upgraded to PrintedAt 4 without a degree-12 witness.
theorem reviewBad2 : XorMagic.PrintedAt 4 := ⟨XorMagic.corrected_at_4.1, fun d _ _ _ => by omega⟩
