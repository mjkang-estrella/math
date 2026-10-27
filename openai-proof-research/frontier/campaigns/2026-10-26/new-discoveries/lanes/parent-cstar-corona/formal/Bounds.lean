import Obstruction

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

namespace CStarCorona

abbrev sourceCStarStructure : CStarAlgebra A := inferInstance

theorem coeff_norm_le : ‖coeff‖ ≤ (1 / 4 : ℝ) := by
  rw [coeff, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr
  intro i
  fin_cases i <;> norm_num

theorem small_perturbation_lower (T : A) (hT : ‖T‖ ≤ (1 / 4 : ℝ)) :
    algebraMap ℝ A (1 / 2) ≤ (1 + T) * star (1 + T) := by
  have hs : IsSelfAdjoint (T + star T) := by
    simp only [IsSelfAdjoint, star_add, star_star]
    exact add_comm _ _
  have hn : ‖T + star T‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖T + star T‖ ≤ ‖T‖ + ‖star T‖ := norm_add_le _ _
      _ ≤ 1 / 2 := by rw [norm_star]; linarith
  have hlo : -(algebraMap ℝ A ‖T + star T‖) ≤ T + star T :=
    hs.neg_algebraMap_norm_le_self
  have hneg : -(algebraMap ℝ A (1 / 2)) ≤ T + star T :=
    (neg_le_neg (algebraMap_mono A hn)).trans hlo
  have hh : algebraMap ℝ A (1 / 2) = (1 : A) + -(algebraMap ℝ A (1 / 2)) := by
    have h : (1 / 2 : ℝ) = 1 - 1 / 2 := by norm_num
    conv_lhs => rw [h]
    rw [map_sub, map_one, sub_eq_add_neg]
  calc
    algebraMap ℝ A (1 / 2) = 1 + -(algebraMap ℝ A (1 / 2)) := hh
    _ ≤ 1 + (T + star T) := by simpa [add_comm] using add_le_add_left hneg 1
    _ ≤ 1 + (T + star T) + T * star T := le_add_of_nonneg_right (mul_star_self_nonneg T)
    _ = (1 + T) * star (1 + T) := by simp only [star_add, star_one]; noncomm_ring

theorem witness_norm_bound (z : A) (hz : ‖z‖ < 1) : ‖witness z‖ ≤ (5 / 4 : ℝ) := by
  have hc : ‖coeff * z‖ ≤ (1 / 4 : ℝ) := by
    calc
      ‖coeff * z‖ ≤ ‖coeff‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (1 / 4 : ℝ) * 1 := mul_le_mul coeff_norm_le hz.le (norm_nonneg _) (by norm_num)
      _ = 1 / 4 := by norm_num
  calc
    ‖witness z‖ ≤ ‖(1 : A)‖ + ‖coeff * z‖ := norm_add_le _ _
    _ ≤ 5 / 4 := by rw [norm_one]; linarith

theorem witness_order_bounds (z : A) (hz : ‖z‖ < 1) :
    algebraMap ℝ A (1 / 2) ≤ witness z * star (witness z) ∧
      algebraMap ℝ A (1 / 2) ≤ star (witness z) * witness z := by
  have hc : ‖coeff * z‖ ≤ (1 / 4 : ℝ) := by
    calc
      ‖coeff * z‖ ≤ ‖coeff‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (1 / 4 : ℝ) * 1 := mul_le_mul coeff_norm_le hz.le (norm_nonneg _) (by norm_num)
      _ = 1 / 4 := by norm_num
  refine ⟨small_perturbation_lower _ hc, ?_⟩
  have hs := small_perturbation_lower (star (coeff * z)) (by rw [norm_star]; exact hc)
  simpa only [witness, star_add, star_one, star_star] using hs

end CStarCorona
