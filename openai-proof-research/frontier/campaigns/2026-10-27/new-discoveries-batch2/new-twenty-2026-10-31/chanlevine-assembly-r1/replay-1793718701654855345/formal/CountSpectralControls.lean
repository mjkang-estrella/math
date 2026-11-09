import CountFinal2
import CountControls
namespace ChanLevine.Round3.Controls

theorem parity_odd : parityCoefficient 3 = 0 := by decide
theorem parity_two : parityCoefficient 2 = -2 := by decide
theorem parity_four : parityCoefficient 4 = 2 := by decide
theorem constant_minus_one : ((dominoMatrix (-1 : ℤ) 1)^4).trace = 2 := by decide
theorem lucas_fixed : lucasTrace (3 : ℤ) 2 4 = 17 := by decide
theorem incorrect_lucas_rejected : lucasTrace (3 : ℤ) 2 4 ≠ 16 := by decide
end ChanLevine.Round3.Controls
