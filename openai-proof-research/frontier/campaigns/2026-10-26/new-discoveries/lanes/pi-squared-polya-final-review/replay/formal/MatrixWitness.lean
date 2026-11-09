import BlockCompression

set_option warningAsError true

open Matrix
open scoped MatrixOrder ComplexOrder

namespace SquaredPolya

noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

def aMat : Mat2 := !![(1025 : ℂ)/2, -1023/2; -1023/2, 1025/2]
def bMat : Mat2 := !![(1024 : ℂ), 0; 0, 1]
def fMat : Mat2 := !![(3073 : ℂ)/4, -1023/4; -1023/4, 1027/4]
def gMat : Mat2 := !![(1025 : ℂ)/2, 0; 0, 1]
def tMat : Mat2 := !![(32 : ℂ), 0; 0, 1]
def aInv : Mat2 := !![(1025 : ℂ)/2048, 1023/2048; 1023/2048, 1025/2048]
def bInv : Mat2 := !![(1 : ℂ)/1024, 0; 0, 1]
def fInv : Mat2 := !![(2054 : ℂ)/1054721, 2046/1054721; 2046/1054721, 6146/1054721]

theorem a_lower : (aMat - 1).PosSemidef := by
  let R : Mat2 := !![(1 : ℂ), -1; 0, 0]
  have heq : aMat - 1 = (1023 / 2 : ℝ) • (Rᴴ * R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [aMat, R, Matrix.mul_apply, Fin.sum_univ_two]
  rw [heq]
  exact (Matrix.posSemidef_conjTranspose_mul_self R).smul (by norm_num : (0 : ℝ) ≤ 1023/2)

theorem a_upper : ((1024 : ℝ) • (1 : Mat2) - aMat).PosSemidef := by
  let R : Mat2 := !![(1 : ℂ), 1; 0, 0]
  have heq : (1024 : ℝ) • (1 : Mat2) - aMat = (1023 / 2 : ℝ) • (Rᴴ * R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [aMat, R, Matrix.mul_apply, Fin.sum_univ_two]
  rw [heq]
  exact (Matrix.posSemidef_conjTranspose_mul_self R).smul (by norm_num : (0 : ℝ) ≤ 1023/2)

theorem b_lower : (bMat - 1).PosSemidef := by
  let R : Mat2 := !![(1 : ℂ), 0; 0, 0]
  have heq : bMat - 1 = (1023 : ℝ) • (Rᴴ * R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [bMat, R, Matrix.mul_apply, Fin.sum_univ_two]
  rw [heq]
  exact (Matrix.posSemidef_conjTranspose_mul_self R).smul (by norm_num : (0 : ℝ) ≤ 1023)

theorem b_upper : ((1024 : ℝ) • (1 : Mat2) - bMat).PosSemidef := by
  let R : Mat2 := !![(0 : ℂ), 0; 0, 1]
  have heq : (1024 : ℝ) • (1 : Mat2) - bMat = (1023 : ℝ) • (Rᴴ * R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [bMat, R, Matrix.mul_apply, Fin.sum_univ_two]
  rw [heq]
  exact (Matrix.posSemidef_conjTranspose_mul_self R).smul (by norm_num : (0 : ℝ) ≤ 1023)

theorem a_posDef : aMat.PosDef := by
  convert (Matrix.PosDef.one (n := Fin 2) (R := ℂ)).add_posSemidef a_lower using 1
  abel

theorem b_posDef : bMat.PosDef := by
  convert (Matrix.PosDef.one (n := Fin 2) (R := ℂ)).add_posSemidef b_lower using 1
  abel

theorem f_eq : fMat = (1 / 2 : ℝ) • (aMat + bMat) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [fMat, aMat, bMat]

theorem g_eq : gMat = (1 / 2 : ℝ) • (bMat + 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [gMat, bMat]

theorem f_posDef : fMat.PosDef := by
  rw [f_eq]
  exact (a_posDef.add b_posDef).smul (by norm_num : (0 : ℝ) < 1/2)

theorem g_posDef : gMat.PosDef := by
  rw [g_eq]
  exact (b_posDef.add Matrix.PosDef.one).smul (by norm_num : (0 : ℝ) < 1/2)

theorem a_inv : aMat⁻¹ = aInv := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [aMat, aInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem b_inv : bMat⁻¹ = bInv := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bMat, bInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem f_inv : fMat⁻¹ = fInv := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fMat, fInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem ab_riccati_numerator :
    (aMat + bMat) * aMat⁻¹ * (aMat + bMat) =
      (1054721 / 2048 : ℝ) • bMat := by
  rw [a_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [aMat, bMat, aInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem t_squared : tMat * tMat = bMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tMat, bMat, Matrix.mul_apply, Fin.sum_univ_two]


end

end SquaredPolya
