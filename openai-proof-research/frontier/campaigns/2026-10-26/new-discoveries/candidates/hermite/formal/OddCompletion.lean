import PreOriginSource
import SourceCompletion
import Comparison

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

theorem source_odd_bulk_proved (m : ℕ) (hm : 1 ≤ m) (x : ℝ)
    (hx : 0 ≤ x) (hq : x ^ 2 < 2 * ((2 * m + 1 : ℕ) : ℝ) + 1) :
    |weightedHermite (2 * m + 1) x| ≤
      sourceCoefficient (2 * m + 1) * sourceEnvelope (2 * m + 1) x := by
  have hE : 7 ≤ 4 * (m : ℝ) + 3 := by
    exact_mod_cast (show 7 ≤ 4 * m + 3 by omega)
  have hA := oddSlopeMagnitude_pos m
  have hf := signedOddValue_hasDerivAt m
  have hg := signedOddSlope_hasDerivAt m
  have hf0 := signedOddValue_zero m
  have hg0 := signedOddSlope_zero m
  by_cases hsmall : x ≤ Real.sqrt (2 / (4 * (m : ℝ) + 3))
  · have hnonneg := odesys_nonneg hE hA hf hg hf0 hg0 x hx hsmall
    have hupper := (sine_comparison hE hA hf hg hf0 hg0 x hx hsmall).2
    exact source_odd_small_of_sine_upper m hm x hx hsmall hnonneg hupper
  · have hloss := energy_loss hE hA hf hg hf0 hg0
    exact source_odd_large_from_loss m x (le_of_lt (lt_of_not_ge hsmall)) hq hloss

theorem source_conjecture_346243 : SourceConjecture346243 :=
  source_conjecture_of_odd_bulk source_odd_bulk_proved

end HermiteEnvelope
