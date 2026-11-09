import CountFinal3
import CountSpectralControls
namespace ChanLevine.Round4.Controls
theorem primitive_one : IsPrimitiveRoot (1 : ℚ) 1 := by
  constructor
  · rfl
  · intro l _; exact one_dvd l
theorem denominator_one : Round3.denominator (1 : ℚ) 1 = 1-Polynomial.X := by
  simpa [Round3.universalDenominator] using primitive_denominator primitive_one (by decide)
theorem trace_one : (Round3.transferProduct (1 : ℚ) 1).trace = 2 := by
  simp [Round3.transferProduct, Round3.orderedProduct, Round3.transferFactor,
    Round3.domino_trace]
  norm_num
end ChanLevine.Round4.Controls
