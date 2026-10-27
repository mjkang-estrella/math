import UnboundedDefs

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CStarSmaleUnbounded

theorem branch_apart (epsilon : ℝ) (he : 0 < epsilon) (t : Time) :
    branch epsilon t ≠ (-branch epsilon) t := by
  have hp : 0 < Real.sqrt ((2 * (t : ℝ) - 1) ^ 2 + epsilon) :=
    Real.sqrt_pos.mpr (by positivity)
  intro h
  have hh := congrArg Complex.re h
  change Real.sqrt ((2 * (t : ℝ) - 1) ^ 2 + epsilon) =
    -Real.sqrt ((2 * (t : ℝ) - 1) ^ 2 + epsilon) at hh
  linarith

theorem critical_complete (epsilon : ℝ) (he : 0 < epsilon) (w : FunctionAlgebra)
    (hw : cubicDeleted (roots epsilon) w = 0) :
    w = branch epsilon ∨ w = -branch epsilon := by
  apply CStarSendov.selection_rigidity_cmap w (branch epsilon) (-branch epsilon)
    (branch_apart epsilon he)
  intro t
  rw [deleted_eq] at hw
  have hh := congrArg (fun f : FunctionAlgebra => f t) hw
  change (3 : ℂ) * (w t - branch epsilon t) * (w t + branch epsilon t) = 0 at hh
  have heq : (w t - branch epsilon t) * (w t + branch epsilon t) = 0 := by
    linear_combination hh / 3
  rcases mul_eq_zero.mp heq with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by simpa only [ContinuousMap.neg_apply] using eq_neg_of_add_eq_zero_left h)

theorem deleted_coordinate (epsilon : ℝ) (he : 0 ≤ epsilon) :
    cubicDeleted (roots epsilon) coordinate = ContinuousMap.const Time (-3 * (epsilon : ℂ)) := by
  rw [deleted_eq]
  ext t
  change (3 : ℂ) * (coordinate t - branch epsilon t) * (coordinate t + branch epsilon t) =
    -3 * (epsilon : ℂ)
  linear_combination -3 * branch_sq epsilon he t

theorem deleted_coordinate_norm (epsilon : ℝ) (he : 0 < epsilon) :
    ‖cubicDeleted (roots epsilon) coordinate‖ = 3 * epsilon := by
  have hv : ‖(-3 : ℂ) * (epsilon : ℂ)‖ = 3 * epsilon := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  rw [deleted_coordinate epsilon he.le]
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ 3 * epsilon)).mpr
    intro t
    exact hv.le
  · have h := (ContinuousMap.const Time (-3 * (epsilon : ℂ))).norm_coe_le_norm timeZero
    change ‖(-3 : ℂ) * (epsilon : ℂ)‖ ≤ _ at h
    rw [hv] at h
    exact h

theorem deleted_coordinate_ne (epsilon : ℝ) (he : 0 < epsilon) :
    cubicDeleted (roots epsilon) coordinate ≠ 0 := by
  intro h
  have hh := congrArg norm h
  rw [deleted_coordinate_norm epsilon he, norm_zero] at hh
  nlinarith

theorem coordinate_norm_le : ‖coordinate‖ ≤ 1 := by
  apply (ContinuousMap.norm_le coordinate (by norm_num)).mpr
  intro t
  change ‖((2 * (t : ℝ) - 1 : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [t.property.1, t.property.2]

theorem branch_norm_le (epsilon : ℝ) (he : epsilon ≤ 1 / 16) :
    ‖branch epsilon‖ ≤ 5 / 4 := by
  apply (ContinuousMap.norm_le (branch epsilon) (by norm_num)).mpr
  intro t
  change ‖(Real.sqrt ((2 * (t : ℝ) - 1) ^ 2 + epsilon) : ℂ)‖ ≤ 5 / 4
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · nlinarith [t.property.1, t.property.2,
      mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2)]

theorem critical_distance_le (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon ≤ 1 / 16)
    (w : FunctionAlgebra) (hw : cubicDeleted (roots epsilon) w = 0) :
    ‖coordinate - w‖ ≤ 9 / 4 := by
  rcases critical_complete epsilon he0 w hw with rfl | rfl
  · calc
      ‖coordinate - branch epsilon‖ ≤ ‖coordinate‖ + ‖branch epsilon‖ := norm_sub_le _ _
      _ ≤ 9 / 4 := by linarith [coordinate_norm_le, branch_norm_le epsilon he1]
  · calc
      ‖coordinate - -branch epsilon‖ ≤ ‖coordinate‖ + ‖-branch epsilon‖ := norm_sub_le _ _
      _ ≤ 9 / 4 := by rw [norm_neg]; linarith [coordinate_norm_le, branch_norm_le epsilon he1]

theorem critical_distance_pos (epsilon : ℝ) (he : 0 < epsilon)
    (w : FunctionAlgebra) (hw : cubicDeleted (roots epsilon) w = 0) :
    0 < ‖coordinate - w‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have hc : coordinate = w := sub_eq_zero.mp hz
  exact deleted_coordinate_ne epsilon he (hc.symm ▸ hw)

end CStarSmaleUnbounded
