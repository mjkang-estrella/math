import PrincipalCompression

namespace KadarYu

open Matrix Finset

/-- Literal lower-right block, with no cyclic-compression assumption. -/
theorem jacobiMatrix_tail_block (r s : ℕ) (diag off : ℕ → ℝ)
    (hd : ∀ i, r ≤ i → diag i = 0) (ho : ∀ i, r ≤ i → off i = 1) :
    ((jacobiMatrix (r + s) diag off).submatrix finSumFinEquiv finSumFinEquiv).submatrix
      Sum.inr Sum.inr = jacobiMatrix s (fun _ => 0) (fun _ => 1) := by
  apply Matrix.ext
  intro i j
  simp [Matrix.submatrix_apply, finSumFinEquiv_apply_right, jacobiMatrix,
    hd (r + i.val) (by omega), ho (r + i.val) (by omega),
    ho (r + j.val) (by omega), Nat.add_assoc]

theorem jacobi_spectralCountAbove_le_head (r s : ℕ) (diag off : ℕ → ℝ)
    (hd : ∀ i, r ≤ i → diag i = 0) (ho : ∀ i, r ≤ i → off i = 1) :
    spectralCountAbove (jacobiMatrix_hermitian (r + s) diag off) 2 ≤ r := by
  let hA := jacobiMatrix_hermitian (r + s) diag off
  have h := spectralCountAbove_two_le_head (n := Fin r) s
    (hA.submatrix finSumFinEquiv) (jacobiMatrix_tail_block r s diag off hd ho)
  rw [spectralCountAbove_submatrix_equiv] at h
  simpa only [Fintype.card_fin] using h

theorem jacobi_spectralCountBelow_le_head (r s : ℕ) (diag off : ℕ → ℝ)
    (hd : ∀ i, r ≤ i → diag i = 0) (ho : ∀ i, r ≤ i → off i = 1) :
    spectralCountBelow (jacobiMatrix_hermitian (r + s) diag off) (-2) ≤ r := by
  let hA := jacobiMatrix_hermitian (r + s) diag off
  have h := spectralCountBelow_neg_two_le_head (n := Fin r) s
    (hA.submatrix finSumFinEquiv) (jacobiMatrix_tail_block r s diag off hd ho)
  rw [spectralCountBelow_submatrix_equiv] at h
  simpa only [Fintype.card_fin] using h

theorem jacobi_spectralCountAbove_succ (diag off : ℕ → ℝ) (c : ℝ) (s : ℕ) :
    spectralCountAbove (jacobiMatrix_hermitian s diag off) c ≤
      spectralCountAbove (jacobiMatrix_hermitian (s + 1) diag off) c := by
  have h := spectralCountAbove_principal ⟨Fin.castSucc, Fin.castSucc_injective s⟩
    (jacobiMatrix_hermitian (s + 1) diag off) c
  exact (spectralCountAbove_congr _ _ (jacobiMatrix_prefix s diag off) c).symm.trans_le h

theorem jacobi_spectralCountBelow_succ (diag off : ℕ → ℝ) (c : ℝ) (s : ℕ) :
    spectralCountBelow (jacobiMatrix_hermitian s diag off) c ≤
      spectralCountBelow (jacobiMatrix_hermitian (s + 1) diag off) c := by
  have h := spectralCountBelow_principal ⟨Fin.castSucc, Fin.castSucc_injective s⟩
    (jacobiMatrix_hermitian (s + 1) diag off) c
  exact (spectralCountBelow_congr _ _ (jacobiMatrix_prefix s diag off) c).symm.trans_le h

theorem jacobi_exterior_counts_stabilize (r : ℕ) (diag off : ℕ → ℝ)
    (hd : ∀ i, r ≤ i → diag i = 0) (ho : ∀ i, r ≤ i → off i = 1) :
    ∃ N a b : ℕ, a ≤ r ∧ b ≤ r ∧ ∀ s, N ≤ s →
      spectralCountAbove (jacobiMatrix_hermitian (r + s) diag off) 2 = a ∧
      spectralCountBelow (jacobiMatrix_hermitian (r + s) diag off) (-2) = b := by
  let f := fun s => spectralCountAbove (jacobiMatrix_hermitian (r + s) diag off) 2
  let g := fun s => spectralCountBelow (jacobiMatrix_hermitian (r + s) diag off) (-2)
  have hf : Monotone f := monotone_nat_of_le_succ fun s => by
    simpa only [f, Nat.add_assoc] using jacobi_spectralCountAbove_succ diag off 2 (r + s)
  have hg : Monotone g := monotone_nat_of_le_succ fun s => by
    simpa only [g, Nat.add_assoc] using jacobi_spectralCountBelow_succ diag off (-2) (r + s)
  have hfb : ∀ s, f s ≤ r := fun s => jacobi_spectralCountAbove_le_head r s diag off hd ho
  have hgb : ∀ s, g s ≤ r := fun s => jacobi_spectralCountBelow_le_head r s diag off hd ho
  obtain ⟨a, N, hN⟩ := converges_of_monotone_of_bounded hf hfb
  obtain ⟨b, M, hM⟩ := converges_of_monotone_of_bounded hg hgb
  refine ⟨max N M, a, b, ?_, ?_, ?_⟩
  · rw [← hN N le_rfl]
    exact hfb N
  · rw [← hM M le_rfl]
    exact hgb M
  · intro s hs
    exact ⟨hN s ((le_max_left N M).trans hs), hM s ((le_max_right N M).trans hs)⟩

end KadarYu
