import Mathlib

namespace PermutationRigidity
open Matrix
open scoped MatrixOrder

def L : Matrix (Fin 1) (Fin 3) ℝ := !![1, 0, 0]
noncomputable def D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 1/2, 1/3]
noncomputable def U : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 3/5, -(4/5); 0, 4/5, 3/5]

noncomputable def stationary (A : Matrix (Fin 1) (Fin 3) ℝ)
    (B V : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Vᵀ * Aᵀ * CFC.rpow (A * V * B * Vᵀ * Aᵀ) (-(1/3 : ℝ)) * A * V

theorem active_block : L * U * D * Uᵀ * Lᵀ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  norm_num [L, U, D, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal, Matrix.vecMul, dotProduct, Matrix.vecHead]

theorem stationary_value : stationary L D U = Matrix.diagonal ![1, 0, 0] := by
  unfold stationary
  rw [active_block]
  simp only [CFC.rpow_eq_pow, CFC.one_rpow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [L, U, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal, Matrix.vecMul, dotProduct, Matrix.vecHead]

theorem orthogonal_left : Uᵀ * U = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [U, Matrix.mul_apply, Fin.sum_univ_succ]

theorem orthogonal_right : U * Uᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [U, Matrix.mul_apply, Fin.sum_univ_succ]

theorem positive_diagonal : D.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num

theorem diagonal_distinct : Function.Injective (fun i => D i i) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [D]

theorem stationary_diagonal : (stationary L D U).IsDiag := by
  rw [stationary_value]
  exact Matrix.isDiag_diagonal _

/-- Stronger obstruction: the rotation is not even an entrywise signed permutation. -/
theorem has_nonpermutation_entry : U 1 1 ≠ 0 ∧ U 1 1 ≠ 1 ∧ U 1 1 ≠ -1 := by
  norm_num [U]

theorem not_permutation : ¬ ∃ p : Equiv.Perm (Fin 3), U = p.permMatrix ℝ := by
  rintro ⟨p, h⟩
  have he := congrFun (congrFun h 1) 1
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix, Matrix.of_apply] at he
  split_ifs at he <;> norm_num [U] at he

theorem rectangular_diagonal : ∀ (i : Fin 1) (j : Fin 3),
    i.val ≠ j.val → L i j = 0 := by
  intro i j h
  fin_cases i
  fin_cases j <;> simp_all [L]

theorem counterexample :
    (∀ (i : Fin 1) (j : Fin 3), i.val ≠ j.val → L i j = 0) ∧
    D.IsDiag ∧ D.PosDef ∧ Function.Injective (fun i => D i i) ∧
    Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
    (L * U * D * Uᵀ * Lᵀ).PosDef ∧ (stationary L D U).IsDiag ∧
    ¬ (∃ p : Equiv.Perm (Fin 3), U = p.permMatrix ℝ) := by
  refine ⟨rectangular_diagonal, Matrix.isDiag_diagonal _, positive_diagonal,
    diagonal_distinct, orthogonal_left, orthogonal_right, ?_, stationary_diagonal,
    not_permutation⟩
  rw [active_block]
  exact Matrix.PosDef.one

end PermutationRigidity
