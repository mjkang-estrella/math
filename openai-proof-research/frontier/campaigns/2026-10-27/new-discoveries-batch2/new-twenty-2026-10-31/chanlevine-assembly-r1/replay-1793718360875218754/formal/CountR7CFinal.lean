import CountR7CGeometric
noncomputable section
open scoped BigOperators
namespace ChanLevine.Round7C
open Round6 Round3 Polynomial
attribute [local instance] Classical.propDecidable

/-- The literal frozen counting convolution, including degree zero. -/
theorem matchingCountConvolution : MatchingCountConvolution := by
  intro n inst hn k m
  simp_rw [completed_matching]
  unfold matchingNumerator matchingSeries
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Matching s
  · rw [ite_eq_left hs, ← map_pow, ← map_pow, ← map_mul, coeff_C_mul,
      chip_convolution, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [ite_eq_left hs]
    ring
  · rw [ite_eq_right hs, coeff_zero]
    symm
    apply Finset.sum_eq_zero
    intro i _
    simp [hs]
end ChanLevine.Round7C

