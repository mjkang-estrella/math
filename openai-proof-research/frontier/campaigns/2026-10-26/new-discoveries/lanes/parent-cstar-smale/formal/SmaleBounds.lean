import SmaleDefs

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CStarSmale

theorem branch_apart (t : Time) : branch t ≠ (-branch) t := by
  have hp : 0 < Real.sqrt ((2 * (t : ℝ) - 1) ^ 2 + 1 / 16) :=
    Real.sqrt_pos.mpr (by positivity)
  intro h
  have hh := congrArg Complex.re h
  change Real.sqrt ((2 * (t : ℝ) - 1) ^ 2 + 1 / 16) =
    -Real.sqrt ((2 * (t : ℝ) - 1) ^ 2 + 1 / 16) at hh
  linarith

theorem critical_complete (w : FunctionAlgebra) (hw : cubicDeleted roots w = 0) :
    w = branch ∨ w = -branch := by
  apply CStarSendov.selection_rigidity_cmap w branch (-branch) branch_apart
  intro t
  rw [deleted_eq] at hw
  have hh := congrArg (fun f : FunctionAlgebra => f t) hw
  change (3 : ℂ) * (w t - branch t) * (w t + branch t) = 0 at hh
  have he : (w t - branch t) * (w t + branch t) = 0 := by
    linear_combination hh / 3
  rcases mul_eq_zero.mp he with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by simpa only [ContinuousMap.neg_apply] using eq_neg_of_add_eq_zero_left h)

theorem deleted_coordinate :
    cubicDeleted roots coordinate = ContinuousMap.const Time (-3 / 16 : ℂ) := by
  rw [deleted_eq]
  ext t
  change (3 : ℂ) * (coordinate t - branch t) * (coordinate t + branch t) = -3 / 16
  linear_combination -3 * branch_sq t

theorem deleted_coordinate_ne : cubicDeleted roots coordinate ≠ 0 := by
  rw [deleted_coordinate]
  intro h
  have hh := congrArg (fun f : FunctionAlgebra => f timeZero) h
  norm_num at hh

theorem deleted_coordinate_norm : ‖cubicDeleted roots coordinate‖ = 3 / 16 := by
  rw [deleted_coordinate]
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 3 / 16)).mpr
    intro t
    change ‖(-3 / 16 : ℂ)‖ ≤ 3 / 16
    norm_num
  · have h := (ContinuousMap.const Time (-3 / 16 : ℂ)).norm_coe_le_norm timeZero
    norm_num at h ⊢
    exact h

theorem coordinate_norm_le : ‖coordinate‖ ≤ 1 := by
  apply (ContinuousMap.norm_le coordinate (by norm_num)).mpr
  intro t
  change ‖((2 * (t : ℝ) - 1 : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [t.property.1, t.property.2]

theorem branch_norm_le : ‖branch‖ ≤ 5 / 4 := by
  apply (ContinuousMap.norm_le branch (by norm_num)).mpr
  intro t
  change ‖(Real.sqrt ((2 * (t : ℝ) - 1) ^ 2 + 1 / 16) : ℂ)‖ ≤ 5 / 4
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · nlinarith [t.property.1, t.property.2,
      mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2)]

theorem distance_plus_le : ‖coordinate - branch‖ ≤ 9 / 4 := by
  calc
    ‖coordinate - branch‖ ≤ ‖coordinate‖ + ‖branch‖ := norm_sub_le _ _
    _ ≤ 9 / 4 := by linarith [coordinate_norm_le, branch_norm_le]

theorem distance_minus_le : ‖coordinate - -branch‖ ≤ 9 / 4 := by
  calc
    ‖coordinate - -branch‖ ≤ ‖coordinate‖ + ‖-branch‖ := norm_sub_le _ _
    _ ≤ 9 / 4 := by simpa only [norm_neg] using
        (show ‖coordinate‖ + ‖branch‖ ≤ 9 / 4 by
          linarith [coordinate_norm_le, branch_norm_le])

end CStarSmale
