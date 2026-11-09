import SourceDefs

set_option autoImplicit false

noncomputable section
open Set

namespace ArcsinhPositive

theorem entropyExpression_eq_binEntropy {u : ℝ} (hu : 0 < u) :
    entropyExpression u = Real.binEntropy (u / (1 + u)) := by
  have hd : 0 < 1 + u := by positivity
  have hsub : 1 - u / (1 + u) = (1 + u)⁻¹ := by field_simp; ring
  rw [Real.binEntropy, hsub, Real.log_inv, Real.log_inv,
    Real.log_inv, Real.log_div (ne_of_gt hu) (ne_of_gt hd)]
  unfold entropyExpression
  field_simp
  ring

theorem entropyExpression_bounds {u : ℝ} (hu : 0 < u) :
    0 < entropyExpression u ∧ entropyExpression u ≤ Real.log 2 := by
  rw [entropyExpression_eq_binEntropy hu]
  have hd : 0 < 1 + u := by positivity
  exact ⟨Real.binEntropy_pos (div_pos hu hd) ((div_lt_one hd).2 (by linarith)),
    Real.binEntropy_le_log_two⟩

end ArcsinhPositive
