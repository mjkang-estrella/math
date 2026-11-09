/-
BiHTrace: spectral trace facts for real Hermitian matrices, used to pass from the
eigenvalue definition of the biharmonic index to traces of inverse matrices.

MathDB 352303 (Z. Lin, arXiv:2110.09931).
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct

open Matrix Unitary

namespace BiH

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral theorem in the real form `A = U * diagonal λ * Uᵀ`. -/
theorem spectral_real (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal hA.eigenvalues *
      (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [conjStarAlgAut_apply, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hd : diagonal (RCLike.ofReal ∘ hA.eigenvalues) = diagonal hA.eigenvalues := by
    rw [RCLike.ofReal_real_eq_id]
    rfl
  rw [hd]

omit [DecidableEq n] in
/-- The `(j,j)` entry of `Uᵀ A U` is the Rayleigh quotient of the `j`-th column of `U`. -/
theorem transpose_mul_mul_apply_diag (A U : Matrix n n ℝ) (j : n) :
    (Uᵀ * A * U) j j = (fun i => U i j) ⬝ᵥ (A *ᵥ fun i => U i j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))

/-- For a unitary matrix `U`, the trace of `A` is the sum of the Rayleigh quotients of
the columns of `U`. -/
theorem trace_eq_sum_dotProduct_col (A U : Matrix n n ℝ)
    (_hU : Uᵀ * U = 1) (hUU : U * Uᵀ = 1) :
    A.trace = ∑ j, (fun i => U i j) ⬝ᵥ (A *ᵥ fun i => U i j) := by
  have h1 : (Uᵀ * A * U).trace = A.trace := by
    rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
  rw [← h1, Matrix.trace]
  exact Finset.sum_congr rfl (fun j _ => transpose_mul_mul_apply_diag A U j)

/-- Eigenvalues of a Hermitian matrix with nonzero determinant are all nonzero. -/
theorem eigenvalues_ne_zero_of_det_ne_zero (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hdet : A.det ≠ 0) (i : n) : hA.eigenvalues i ≠ 0 := by
  have hprod : ∏ j, hA.eigenvalues j ≠ 0 := by
    intro h0
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    simpa using h0
  exact Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)

/-- The inverse of an invertible Hermitian matrix in its eigenbasis. -/
theorem inv_eq_spectral (A : Matrix n n ℝ) (hA : A.IsHermitian) (hdet : A.det ≠ 0) :
    A⁻¹ = (hA.eigenvectorUnitary : Matrix n n ℝ) *
        diagonal (fun i => (hA.eigenvalues i)⁻¹) *
        star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
  let U : Matrix n n ℝ := ↑hA.eigenvectorUnitary
  let D : Matrix n n ℝ := diagonal hA.eigenvalues
  let D' : Matrix n n ℝ := diagonal (fun i => (hA.eigenvalues i)⁻¹)
  have hne : ∀ i, hA.eigenvalues i ≠ 0 := eigenvalues_ne_zero_of_det_ne_zero A hA hdet
  have hUtU : star U * U = 1 := coe_star_mul_self hA.eigenvectorUnitary
  have hUU : U * star U = 1 := coe_mul_star_self hA.eigenvectorUnitary
  have hAeq : A = U * D * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [conjStarAlgAut_apply]
    have hd : diagonal (RCLike.ofReal ∘ hA.eigenvalues) = D := by
      rw [RCLike.ofReal_real_eq_id]
      rfl
    rw [hd]
  have hDD' : D * D' = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have hfun : (fun i => hA.eigenvalues i * (hA.eigenvalues i)⁻¹) = fun _ => (1 : ℝ) := by
      funext i
      exact mul_inv_cancel₀ (hne i)
    rw [hfun, Matrix.diagonal_one]
  have hmul : A * (U * D' * star U) = 1 := by
    rw [hAeq]
    calc (U * D * star U) * (U * D' * star U)
        = U * D * (star U * U) * D' * star U := by simp only [Matrix.mul_assoc]
      _ = U * D * 1 * D' * star U := by rw [hUtU]
      _ = U * (D * D') * star U := by simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = U * 1 * star U := by rw [hDD']
      _ = 1 := by rw [Matrix.mul_one, hUU]
  exact Matrix.inv_eq_right_inv hmul

/-- Trace of the inverse in terms of the eigenvalues. -/
theorem trace_inv_eq_sum_inv (A : Matrix n n ℝ) (hA : A.IsHermitian) (hdet : A.det ≠ 0) :
    A⁻¹.trace = ∑ i, (hA.eigenvalues i)⁻¹ := by
  let U : Matrix n n ℝ := ↑hA.eigenvectorUnitary
  have hUtU : star U * U = 1 := coe_star_mul_self hA.eigenvectorUnitary
  rw [inv_eq_spectral A hA hdet, Matrix.trace_mul_cycle, hUtU, Matrix.one_mul,
    Matrix.trace_diagonal]

/-- Trace of the square of the inverse in terms of the eigenvalues. -/
theorem trace_inv_sq_eq_sum_inv_sq (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hdet : A.det ≠ 0) :
    (A⁻¹ * A⁻¹).trace = ∑ i, ((hA.eigenvalues i)⁻¹) ^ 2 := by
  let U : Matrix n n ℝ := ↑hA.eigenvectorUnitary
  let D' : Matrix n n ℝ := diagonal (fun i => (hA.eigenvalues i)⁻¹)
  have hUtU : star U * U = 1 := coe_star_mul_self hA.eigenvectorUnitary
  have hmul : (U * D' * star U) * (U * D' * star U) = U * (D' * D') * star U := by
    calc (U * D' * star U) * (U * D' * star U)
        = U * D' * (star U * U) * D' * star U := by simp only [Matrix.mul_assoc]
      _ = U * D' * 1 * D' * star U := by rw [hUtU]
      _ = U * (D' * D') * star U := by simp only [Matrix.mul_assoc, Matrix.mul_one]
  have hsq : D' * D' = diagonal (fun i => ((hA.eigenvalues i)⁻¹) ^ 2) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  rw [inv_eq_spectral A hA hdet, hmul, hsq, Matrix.trace_mul_cycle, hUtU, Matrix.one_mul,
    Matrix.trace_diagonal]

end BiH
