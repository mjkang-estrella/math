import CountFinal4
import CountR4Controls
namespace ChanLevine.Round5.Controls
example : Round3.parityCoefficient 2 = -2 := by decide
example : Round3.parityCoefficient 4 = 2 := by decide
example : Round3.parityCoefficient 3 = 0 := by decide
example : ((Round3.transferProduct (1 : ℚ) 2).trace).coeff 2 = -2 := by
  simpa [Round3.parityCoefficient] using
    (primitive_top (z := (1 : ℚ)) (e := 2) (by norm_num))
example : Round3.PrimitivePeriodData := primitivePeriodData
end ChanLevine.Round5.Controls
