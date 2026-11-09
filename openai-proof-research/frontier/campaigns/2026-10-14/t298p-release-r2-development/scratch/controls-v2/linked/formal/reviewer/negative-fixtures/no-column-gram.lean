import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace T298P
noncomputable section
open scoped BigOperators

/-- Real coefficient columns orthonormal; the vectors need not be orthogonal. -/
theorem coefficient_isometry {Q A E : Type*} [Fintype Q] [Fintype A]
    [DecidableEq A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Q → A → ℝ) (xi : A → E)
     :
    ∑ q, ‖∑ a, C q a • xi a‖ ^ 2 = ∑ a, ‖xi a‖ ^ 2 := by
  simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  calc
    _ = ∑ a, ∑ b, (∑ q, C q a * C q b) * inner ℝ (xi a) (xi b) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by simp

end
end T298P
