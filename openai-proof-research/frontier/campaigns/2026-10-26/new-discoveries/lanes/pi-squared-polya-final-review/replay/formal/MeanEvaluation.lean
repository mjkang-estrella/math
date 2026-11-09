import MatrixWitness

set_option warningAsError true

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace SquaredPolya

def aFactor : ℝ := Real.sqrt (2048 / 1054721)
def bFactor : ℝ := Real.sqrt (4100 / 1054721)
def abMean : Mat2 := aFactor • (aMat + bMat)

theorem aFactor_sq : aFactor * aFactor = (2048 / 1054721 : ℝ) :=
  Real.mul_self_sqrt (by norm_num)

theorem bFactor_sq : bFactor * bFactor = (4100 / 1054721 : ℝ) :=
  Real.mul_self_sqrt (by norm_num)

theorem abMean_posSemidef : abMean.PosSemidef :=
  (a_posDef.posSemidef.add b_posDef.posSemidef).smul (Real.sqrt_nonneg _)

theorem abMean_riccati : abMean * aMat⁻¹ * abMean = bMat := by
  simp only [abMean, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [ab_riccati_numerator, smul_smul, aFactor_sq]
  norm_num

theorem geometricMean_ab : geometricMean aMat bMat = abMean :=
  geometricMean_eq_of_riccati a_posDef abMean_posSemidef abMean_riccati

theorem t_posSemidef : tMat.PosSemidef := by
  have heq : tMat = (1 / 33 : ℝ) • (bMat + (32 : ℝ) • (1 : Mat2)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [tMat, bMat]
  rw [heq]
  exact (b_posDef.posSemidef.add (Matrix.PosSemidef.one.smul
    (by norm_num : (0 : ℝ) ≤ 32))).smul (by norm_num : (0 : ℝ) ≤ 1/33)

theorem t_riccati : tMat * bMat⁻¹ * tMat = 1 := by
  rw [b_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tMat, bInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem geometricMean_b_one : geometricMean bMat (1 : Mat2) = tMat :=
  geometricMean_eq_of_riccati b_posDef t_posSemidef t_riccati

theorem gf_cayley : gMat * fMat⁻¹ * gMat =
    (1058821 / 1054721 : ℝ) • gMat - (4100 / 1054721 : ℝ) • fMat := by
  rw [f_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gMat, fMat, fInv, Matrix.mul_apply, Fin.sum_univ_two]


end SquaredPolya
