import PrincipalMultiplicity

namespace KadarYu

open Matrix Finset Polynomial

theorem unitSquaredPath_polynomial (c : ℝ) (hc : c ^ 2 = 1) (s : ℕ) :
    jacobiPolynomial (fun _ => 0) (fun _ => c) s =
      jacobiPolynomial (fun _ => 0) (fun _ => 1) s := by
  induction s using Nat.twoStepInduction with
  | zero => simp [jacobiPolynomial_zero]
  | one =>
    have hm (d : ℝ) : jacobiMatrix 1 (fun _ => 0) (fun _ => d) = 0 := by
      apply Matrix.ext
      intro i j
      fin_cases i
      fin_cases j
      simp [jacobiMatrix]
    simp only [jacobiPolynomial, hm]
  | more s ih0 ih1 =>
    rw [jacobiPolynomial_recurrence, jacobiPolynomial_recurrence, ih0, ih1]
    simp [hc]

theorem unitSquaredPath_eigenvalues (c : ℝ) (hc : c ^ 2 = 1) (s : ℕ) (i : Fin s) :
    (jacobiMatrix_hermitian s (fun _ => 0) (fun _ => c)).eigenvalues i ∈
      Set.Ioo (-2 : ℝ) 2 := by
  let hP := jacobiMatrix_hermitian s (fun _ => 0) (fun _ => c)
  have hm : hP.eigenvalues i ∈ (jacobiMatrix s (fun _ => 0) (fun _ => c)).charpoly.roots := by
    rw [hP.roots_charpoly_eq_eigenvalues]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hz := (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hm
  change (jacobiPolynomial (fun _ => 0) (fun _ => c) s).eval (hP.eigenvalues i) = 0 at hz
  rw [unitSquaredPath_polynomial c hc] at hz
  exact unitPath_root_in_band hz

def headTailSplitEquiv (h s : ℕ) : Fin (h + 1) ⊕ Fin s ≃ Fin (h + s + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

theorem headTail_tail_equiv (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) (s : ℕ) :
    ((headTailMatrix h A c s).submatrix (headTailSplitEquiv h s)
      (headTailSplitEquiv h s)).submatrix Sum.inr Sum.inr =
      jacobiMatrix s (fun _ => 0) (fun _ => c) := headTailMatrix_tail_block h A c s

theorem headTail_counts_bounds (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c : ℝ) (hc : c ^ 2 = 1) (s : ℕ) :
    spectralCountAbove (headTailMatrix_hermitian h hA c s) 2 ≤ h + 1 ∧
      spectralCountBelow (headTailMatrix_hermitian h hA c s) (-2) ≤ h + 1 := by
  let hM := headTailMatrix_hermitian h hA c s
  let hS := hM.submatrix (headTailSplitEquiv h s)
  have htail := headTail_tail_equiv h A c s
  constructor
  · have ht : ∀ y : EuclideanSpace ℝ (Fin s),
        inner ℝ y ((Matrix.toEuclideanLin ((headTailMatrix h A c s).submatrix
          (headTailSplitEquiv h s) (headTailSplitEquiv h s) |>.submatrix Sum.inr Sum.inr)) y)
          ≤ 2 * ‖y‖ ^ 2 := by
      intro y
      rw [htail]
      exact quadratic_le_of_eigenvalues_le (jacobiMatrix_hermitian s _ _) 2
        (fun i => (unitSquaredPath_eigenvalues c hc s i).2.le) y
    have hh := spectralCountAbove_le_head hS 2 ht
    exact (spectralCountAbove_submatrix_equiv (headTailSplitEquiv h s) hM 2).symm.trans_le
      (by simpa only [Fintype.card_fin] using hh)
  · have ht : ∀ y : EuclideanSpace ℝ (Fin s),
        -2 * ‖y‖ ^ 2 ≤ inner ℝ y ((Matrix.toEuclideanLin ((headTailMatrix h A c s).submatrix
          (headTailSplitEquiv h s) (headTailSplitEquiv h s) |>.submatrix Sum.inr Sum.inr)) y) := by
      intro y
      rw [htail]
      exact quadratic_ge_of_eigenvalues_ge (jacobiMatrix_hermitian s _ _) (-2)
        (fun i => (unitSquaredPath_eigenvalues c hc s i).1.le) y
    have hh := spectralCountBelow_le_head hS (-2) ht
    exact (spectralCountBelow_submatrix_equiv (headTailSplitEquiv h s) hM (-2)).symm.trans_le
      (by simpa only [Fintype.card_fin] using hh)

theorem headTail_counts_succ (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c t : ℝ) (s : ℕ) :
    spectralCountAbove (headTailMatrix_hermitian h hA c s) t ≤
      spectralCountAbove (headTailMatrix_hermitian h hA c (s + 1)) t ∧
    spectralCountBelow (headTailMatrix_hermitian h hA c s) t ≤
      spectralCountBelow (headTailMatrix_hermitian h hA c (s + 1)) t := by
  let hM := headTailMatrix_hermitian h hA c (s + 1)
  constructor
  · have hh := spectralCountAbove_principal
      ⟨Fin.castSucc, Fin.castSucc_injective (h + s + 1)⟩ hM t
    exact (spectralCountAbove_congr _ _ (headTailMatrix_prefix h A c s) t).symm.trans_le hh
  · have hh := spectralCountBelow_principal
      ⟨Fin.castSucc, Fin.castSucc_injective (h + s + 1)⟩ hM t
    exact (spectralCountBelow_congr _ _ (headTailMatrix_prefix h A c s) t).symm.trans_le hh

theorem headTail_exterior_stabilize (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c : ℝ) (hc : c ^ 2 = 1) :
    ∃ N C : ℕ, C ≤ 2 * (h + 1) ∧ ∀ s, N ≤ s →
      exteriorRootCount (headTailPolynomial h A c s) = C := by
  let f := fun s => spectralCountAbove (headTailMatrix_hermitian h hA c s) 2
  let g := fun s => spectralCountBelow (headTailMatrix_hermitian h hA c s) (-2)
  have hf : Monotone f := monotone_nat_of_le_succ fun s => (headTail_counts_succ h hA c 2 s).1
  have hg : Monotone g := monotone_nat_of_le_succ fun s => (headTail_counts_succ h hA c (-2) s).2
  have hfb : ∀ s, f s ≤ h + 1 := fun s => (headTail_counts_bounds h hA c hc s).1
  have hgb : ∀ s, g s ≤ h + 1 := fun s => (headTail_counts_bounds h hA c hc s).2
  obtain ⟨a, N, hN⟩ := converges_of_monotone_of_bounded hf hfb
  obtain ⟨b, M, hM⟩ := converges_of_monotone_of_bounded hg hgb
  refine ⟨max N M, a + b, ?_, ?_⟩
  · have ha : a ≤ h + 1 := by rw [← hN N le_rfl]; exact hfb N
    have hb : b ≤ h + 1 := by rw [← hM M le_rfl]; exact hgb M
    omega
  · intro s hs
    rw [exteriorRootCount_eq, headTailPolynomial,
      rootCountAbove_charpoly (headTailMatrix_hermitian h hA c s),
      rootCountBelow_charpoly (headTailMatrix_hermitian h hA c s)]
    exact congrArg₂ (· + ·) (hN s ((le_max_left N M).trans hs))
      (hM s ((le_max_right N M).trans hs))

end KadarYu
