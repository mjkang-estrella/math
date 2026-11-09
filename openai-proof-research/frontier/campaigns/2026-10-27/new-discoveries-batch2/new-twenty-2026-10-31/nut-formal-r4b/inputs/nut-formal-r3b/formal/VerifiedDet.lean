import Mathlib.LinearAlgebra.Matrix.Adjugate
namespace Nut8
/-- Sparse Laplace evaluation with a dimension-indexed matrix: no malformed list inputs. -/
noncomputable def sparseDet : (n : ℕ) → Matrix (Fin n) (Fin n) ℤ → ℤ
  | 0, _ => 1
  | n+1, A => ∑ j : Fin (n+1), if A 0 j = 0 then 0 else
      (-1) ^ (j : ℕ) * A 0 j * sparseDet n (A.submatrix Fin.succ j.succAbove)

theorem sparseDet_eq_det (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    sparseDet n A = A.det := by
  induction n with
  | zero => simp [sparseDet, Matrix.det_isEmpty]
  | succ n ih =>
    rw [sparseDet, Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · simp [h]
    · rw [ih]

/-- Every principal cofactor is computed by the verified evaluator. -/
theorem sparseDet_principal (n : ℕ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (i : Fin (n+1)) :
    sparseDet n (A.submatrix i.succAbove i.succAbove) = A.adjugate i i := by
  rw [sparseDet_eq_det, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [pow_add, ← mul_pow]
end Nut8
