import InverseCertificates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
set_option autoImplicit false
namespace TraceInverse
open Matrix
private theorem list_sum_range (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

def intMatrix (n : ℕ) (a : Data) : Matrix (Fin n) (Fin n) ℤ := fun i j => entry a i.val j.val

theorem checked_matrix_product (a b : Data) (n : ℕ) (d : ℤ)
    (h : checker a b n d = true) :
    intMatrix n a * intMatrix n b = d • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  ext i j
  have hh := checker_sound a b n d h i.val j.val i.isLt j.isLt
  simp only [dot, list_sum_range] at hh
  simp only [Matrix.mul_apply, intMatrix, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun k => entry a i.val k * entry b k j.val)] at hh
  simpa only [Fin.val_inj, mul_ite, mul_one, mul_zero] using hh

/-- Generic sound algebraic bridge used after checking an actual evaluation matrix. -/
theorem injective_of_scaled_inverse {K : Type*} [Field K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (d : K) (hd : d ≠ 0)
    (h : A * B = d • (1 : Matrix (Fin n) (Fin n) K)) :
    Function.Injective A.mulVec := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  apply isUnit_iff_exists_inv.mpr
  refine ⟨d⁻¹ • B, ?_⟩
  rw [Matrix.mul_smul, h, smul_smul, inv_mul_cancel₀ hd, one_smul]
#print axioms checked_matrix_product
#print axioms injective_of_scaled_inverse
end TraceInverse
