import Mathlib

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open Matrix

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

theorem det_one_add_two_outer (x y z w : n → K) :
    (1 + vecMulVec x y + vecMulVec z w).det =
      (1 + y ⬝ᵥ x) * (1 + w ⬝ᵥ z) - (y ⬝ᵥ z) * (w ⬝ᵥ x) := by
  let U : Matrix n (Fin 2) K := fun i => ![x i, z i]
  let V : Matrix (Fin 2) n K := ![y, w]
  have hUV : U * V = vecMulVec x y + vecMulVec z w := by
    ext i j
    change (∑ k : Fin 2, U i k * V k j) = x i * y j + z i * w j
    simp [U, V, Fin.sum_univ_two]
  have hVU : V * U = !![y ⬝ᵥ x, y ⬝ᵥ z; w ⬝ᵥ x, w ⬝ᵥ z] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      change (∑ k, V _ k * U k _) = _ <;> simp [U, V, dotProduct]
  rw [add_assoc, ← hUV, Matrix.det_one_add_mul_comm, hVU]
  simp [Matrix.det_fin_two]

theorem inverse_skew (B R : Matrix n n K) (t : K)
    (hleft : R * (1 - t • B) = 1) :
    R - R.transpose = t • (R * (B - B.transpose) * R.transpose) := by
  have ht : (1 - t • B).transpose * R.transpose = 1 := by
    simpa using congrArg Matrix.transpose hleft
  calc
    R - R.transpose = R * ((1 - t • B).transpose - (1 - t • B)) * R.transpose := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc R _ R.transpose,
        ht, Matrix.mul_one, hleft, Matrix.one_mul]
    _ = t • (R * (B - B.transpose) * R.transpose) := by
      have hd : (1 - t • B).transpose - (1 - t • B) = t • (B - B.transpose) := by
        simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul]
        module
      rw [hd, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq n] in
theorem dot_outer_mulVec (x y z w : n → K) :
    x ⬝ᵥ (vecMulVec y z *ᵥ w) = (x ⬝ᵥ y) * (z ⬝ᵥ w) := by
  rw [dotProduct_mulVec, Matrix.vecMul_vecMulVec, smul_dotProduct, smul_eq_mul]

theorem resolvent_pair_identity (B R : Matrix n n K) (t : K) (u v : n → K)
    (hleft : R * (1 - t • B) = 1)
    (hskew : B - B.transpose = vecMulVec u v - vecMulVec v u) :
    v ⬝ᵥ (R *ᵥ u) - u ⬝ᵥ (R *ᵥ v) =
      t * ((v ⬝ᵥ (R *ᵥ u)) * (u ⬝ᵥ (R *ᵥ v)) -
        (v ⬝ᵥ (R *ᵥ v)) * (u ⬝ᵥ (R *ᵥ u))) := by
  have hm : R - R.transpose = t •
      (vecMulVec (R *ᵥ u) (R *ᵥ v) - vecMulVec (R *ᵥ v) (R *ᵥ u)) := by
    rw [inverse_skew B R t hleft, hskew, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMulVec_mul, Matrix.vecMul_transpose, Matrix.vecMul_transpose]
  have hv := congrArg (fun M : Matrix n n K => v ⬝ᵥ (M *ᵥ u)) hm
  simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, dot_outer_mulVec,
    Matrix.dotProduct_transpose_mulVec] at hv
  simpa only [dotProduct_comm (R *ᵥ v) u, dotProduct_comm (R *ᵥ u) u] using hv

theorem det_add_two_outer (Q R : Matrix n n K) (hQR : Q * R = 1)
    (x y z w : n → K) :
    (Q + vecMulVec x y + vecMulVec z w).det = Q.det *
      ((1 + y ⬝ᵥ (R *ᵥ x)) * (1 + w ⬝ᵥ (R *ᵥ z)) -
        (y ⬝ᵥ (R *ᵥ z)) * (w ⬝ᵥ (R *ᵥ x))) := by
  have hf : Q * (1 + vecMulVec (R *ᵥ x) y + vecMulVec (R *ᵥ z) w) =
      Q + vecMulVec x y + vecMulVec z w := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_one,
      Matrix.mul_vecMulVec, Matrix.mul_vecMulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQR,
      Matrix.one_mulVec, Matrix.one_mulVec]
  rw [← hf, Matrix.det_mul, det_one_add_two_outer]

variable [CharZero K]

theorem determinant_spectral_collapse (B R : Matrix n n K) (t lam xi gamma : K)
    (u v : n → K)
    (hleft : R * (1 - t • B) = 1)
    (hright : (1 - t • B) * R = 1)
    (hdet : (1 - t • B).det = 1)
    (hskew : B - B.transpose = vecMulVec u v - vecMulVec v u)
    (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) :
    (1 - t • (B + ((lam + xi - 1) / 2) • vecMulVec u v +
      ((lam - xi + 1) / 2) • vecMulVec v u)).det =
      1 - lam * t / 2 * (v ⬝ᵥ (R *ᵥ u) + u ⬝ᵥ (R *ᵥ v)) -
        gamma * lam * t / 4 * (v ⬝ᵥ (R *ᵥ u) - u ⬝ᵥ (R *ᵥ v)) := by
  have hf : 1 - t • (B + ((lam + xi - 1) / 2) • vecMulVec u v +
      ((lam - xi + 1) / 2) • vecMulVec v u) =
      (1 - t • B) + vecMulVec ((-t * ((lam + xi - 1) / 2)) • u) v +
        vecMulVec ((-t * ((lam - xi + 1) / 2)) • v) u := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
    ring
  rw [hf, det_add_two_outer _ R hright, hdet, one_mul]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hp := resolvent_pair_identity B R t u v hleft hskew
  linear_combination t * (gamma * lam / 4 - (xi - 1) / 2) * hp -
    t ^ 2 * ((v ⬝ᵥ (R *ᵥ u)) * (u ⬝ᵥ (R *ᵥ v)) -
      (v ⬝ᵥ (R *ᵥ v)) * (u ⬝ᵥ (R *ᵥ u))) / 4 * hcurve

end PeakonCoefficients
