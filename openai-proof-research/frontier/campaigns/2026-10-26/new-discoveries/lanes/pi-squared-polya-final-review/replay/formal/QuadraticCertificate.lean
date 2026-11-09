import OutputEvaluation
import RadicalSign

set_option warningAsError true

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace SquaredPolya

def qForm : Mat2 →ₗ[ℝ] ℝ where
  toFun M := (M 0 0 + 2 * M 0 1 + 2 * M 1 0 + 4 * M 1 1).re
  map_add' M N := by simp [mul_add]; ring
  map_smul' c M := by
    simp [Complex.real_smul, Complex.mul_re]
    ring

def testVector : Fin 2 → ℂ := ![1, 2]

theorem qForm_eq_dotProduct (M : Mat2) :
    qForm M = (star testVector ⬝ᵥ (M *ᵥ testVector)).re := by
  simp [qForm, testVector, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem qForm_nonneg {M : Mat2} (hM : M.PosSemidef) : 0 ≤ qForm M := by
  rw [qForm_eq_dotProduct]
  exact hM.re_dotProduct_nonneg testVector

theorem qForm_f_squared : qForm (fMat * fMat) = (1058845 / 8 : ℝ) := by
  norm_num [qForm, fMat, Matrix.mul_apply, Fin.sum_univ_two]
theorem qForm_ft : qForm (fMat * tMat) = (17463 / 2 : ℝ) := by
  norm_num [qForm, fMat, tMat, Matrix.mul_apply, Fin.sum_univ_two]
theorem qForm_tf : qForm (tMat * fMat) = (17463 / 2 : ℝ) := by
  norm_num [qForm, fMat, tMat, Matrix.mul_apply, Fin.sum_univ_two]
theorem qForm_t_squared : qForm (tMat * tMat) = (1028 : ℝ) := by
  norm_num [qForm, tMat, Matrix.mul_apply, Fin.sum_univ_two]
theorem qForm_g_squared : qForm (gMat * gMat) = (1050641 / 4 : ℝ) := by
  norm_num [qForm, gMat, Matrix.mul_apply, Fin.sum_univ_two]
theorem qForm_gf : qForm (gMat * fMat) = (1056799 / 8 : ℝ) := by
  norm_num [qForm, gMat, fMat, Matrix.mul_apply, Fin.sum_univ_two]
theorem qForm_fg : qForm (fMat * gMat) = (1056799 / 8 : ℝ) := by
  norm_num [qForm, gMat, fMat, Matrix.mul_apply, Fin.sum_univ_two]

def imageMean : Mat2 := aFactor • fMat + (1 / 2 : ℝ) • tMat

theorem qForm_imageMean_squared : qForm (imageMean * imageMean) =
    (2048 / 1054721 : ℝ) * (1058845 / 8) + aFactor * (17463 / 2) + 257 := by
  simp only [imageMean, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_smul, map_add, LinearMap.map_smul_of_tower, smul_eq_mul]
  rw [qForm_f_squared, qForm_ft, qForm_tf, qForm_t_squared, aFactor_sq]
  ring

theorem qForm_outputMean_squared : qForm (outputMean * outputMean) =
    ((1050641 / 4 : ℝ) + bFactor * (1056799 / 4) +
      (4100 / 1054721) * (1058845 / 8)) / rho := by
  simp only [outputMean, outputNumerator, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, smul_add, smul_smul, map_add, LinearMap.map_smul_of_tower, smul_eq_mul]
  rw [qForm_g_squared, qForm_gf, qForm_fg, qForm_f_squared]
  have hc : cFactor ^ 2 = rho⁻¹ := by nlinarith [cFactor_mul_self]
  have hb : bFactor ^ 2 = (4100 / 1054721 : ℝ) := by nlinarith [bFactor_sq]
  calc
    _ = cFactor ^ 2 * ((1050641 / 4 : ℝ) + bFactor * (1056799 / 4) +
        bFactor ^ 2 * (1058845 / 8)) := by ring
    _ = _ := by rw [hc, hb]; ring

theorem matrix_defect_qForm :
    qForm ((1025 / 64 : ℝ)^2 • (imageMean * imageMean) - outputMean * outputMean) =
      scalarDefect := by
  rw [map_sub, LinearMap.map_smul_of_tower, smul_eq_mul,
    qForm_imageMean_squared, qForm_outputMean_squared]
  rfl

theorem matrix_defect_not_posSemidef :
    ¬ ((1025 / 64 : ℝ)^2 • (imageMean * imageMean) -
      outputMean * outputMean).PosSemidef := by
  intro h
  have hn := qForm_nonneg h
  rw [matrix_defect_qForm] at hn
  linarith [scalarDefect_lt]


end SquaredPolya
