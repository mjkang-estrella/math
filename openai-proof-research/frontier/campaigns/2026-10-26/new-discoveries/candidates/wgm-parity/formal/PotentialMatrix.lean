import LogSemantics

open scoped BigOperators

namespace WGMParity

noncomputable def terminalMatrix {L I : Type*} [Fintype I]
    (child : I × Bool → L ⊕ I) : Matrix I L ℝ := by
  classical
  exact fun i j => ∑ b : Bool, if child (i, b) = Sum.inl j then 1 else 0

theorem terminalMatrix_mulVec {L I : Type*} [Fintype L] [Fintype I]
    (child : I × Bool → L ⊕ I) (u : L → ℝ) (i : I) :
    (terminalMatrix child).mulVec u i =
      ∑ b : Bool, Sum.elim u (fun _ : I => (0 : ℝ)) (child (i, b)) := by
  classical
  simp only [terminalMatrix, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  cases h : child (i, b) with
  | inl j => simp
  | inr j => simp

theorem flowMatrix_transpose_mulVec {L I : Type*} [Fintype I]
    (child : I × Bool → L ⊕ I) (z : I → ℝ) (i : I) :
    (flowMatrix child).transpose.mulVec z i = 2 * z i -
      ∑ b : Bool, Sum.elim (fun _ : L => (0 : ℝ)) z (child (i, b)) := by
  classical
  simp only [flowMatrix, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
    sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp [ite_mul]
  · simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    cases h : child (i, b) with
    | inl j => simp
    | inr j => simp

theorem potential_of_matrix_solution {L I : Type*} [Fintype L] [Fintype I]
    (child : I × Bool → L ⊕ I) (u : L → ℝ) (z : I → ℝ)
    (hz : (flowMatrix child).transpose.mulVec z = (terminalMatrix child).mulVec u) :
    ∀ i, 2 * Sum.elim u z (Sum.inr i) =
      Sum.elim u z (child (i, false)) + Sum.elim u z (child (i, true)) := by
  intro i
  have hi := congrFun hz i
  rw [flowMatrix_transpose_mulVec, terminalMatrix_mulVec] at hi
  simp only [Fintype.sum_bool] at hi
  cases h0 : child (i, false) <;> cases h1 : child (i, true) <;>
    simp [h0, h1] at hi ⊢ <;> linarith

theorem exists_potential_solution {L I : Type*} [Fintype L] [Fintype I]
    (child : I × Bool → L ⊕ I) (hc : Function.Injective child) (u : L → ℝ) :
    ∃ z : I → ℝ, (flowMatrix child).transpose.mulVec z = (terminalMatrix child).mulVec u := by
  classical
  have hu : IsUnit (flowMatrix child) :=
    Matrix.mulVec_injective_iff_isUnit.mp (flowMatrix_mulVec_injective child hc)
  have ht : IsUnit (flowMatrix child).transpose := by
    rwa [Matrix.isUnit_transpose]
  exact (Matrix.mulVec_surjective_iff_isUnit.mpr ht) _

theorem terminalMatrix_vecMul {L I : Type*} [Fintype L] [Fintype I]
    (child : I × Bool → L ⊕ I) (flow : I → ℝ) (j : L) :
    Matrix.vecMul flow (terminalMatrix child) j = inputFlow child flow (Sum.inl j) := by
  classical
  simp only [Matrix.vecMul, dotProduct, terminalMatrix, inputFlow,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

end WGMParity
