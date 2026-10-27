import SourceDefs

open scoped Matrix.Norms.Operator ComplexOrder MatrixOrder
open Matrix
namespace LinMajorization
set_option maxRecDepth 4000
set_option maxHeartbeats 0

theorem lower_isUnit (l m n : ℂ) : IsUnit (lower l m n) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simp [lower, Matrix.det_fin_three]

theorem A_factor : A =
    lower (-37/28) (-230/387) (56/387) *
    diagonal ![(3/10:ℂ),597/7840,395611/499230] *
    star (lower (-37/28) (-230/387) (56/387)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, lower, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, map_ofNat, Matrix.diagonal_apply]

theorem A_posDef : A.PosDef := by
  rw [A_factor]
  apply (lower_isUnit _ _ _).posDef_star_right_conjugate_iff.mpr
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff]

theorem B_factor : B =
    lower (4027/6224) 0 0 * diagonal ![(1742720/83779:ℂ),903/778,0] *
    star (lower (4027/6224) 0 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B, lower, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, map_ofNat, Matrix.diagonal_apply]

theorem B_posSemidef : B.PosSemidef := by
  rw [B_factor]
  apply (lower_isUnit _ _ _).posSemidef_star_right_conjugate_iff.mpr
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff]

theorem Q_star_mul : star Q * Q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, map_ofNat, Matrix.diagonal_apply]

theorem Q_mul_star : Q * star Q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, map_ofNat, Matrix.diagonal_apply]

theorem AB_eq : A*B = Q*D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A,B,Q,D, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem BA_eq : B*A = D*star Q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A,B,Q,D, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, map_ofNat, Matrix.diagonal_apply]

end LinMajorization
