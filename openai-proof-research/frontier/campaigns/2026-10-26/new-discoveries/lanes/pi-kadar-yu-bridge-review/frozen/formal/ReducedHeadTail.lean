import HeadTailDensity

namespace KadarYu

open Matrix Finset Polynomial

theorem exteriorRootCount_mul {F p : Polynomial ℝ} (hF : F ≠ 0) (hp : p ≠ 0) :
    exteriorRootCount (F * p) = exteriorRootCount F + exteriorRootCount p := by
  classical
  simp only [exteriorRootCount, Polynomial.roots_mul (mul_ne_zero hF hp),
    Multiset.filter_add, Multiset.card_add]

theorem reduced_headTail_squarefree (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c : ℝ) (F : Polynomial ℝ) (p : ℕ → Polynomial ℝ)
    (hF : F.Monic) (hp : ∀ s, (p s).Monic)
    (hfac : ∀ s, headTailPolynomial h A c s = F * p s)
    (hcop : ∀ s, IsCoprime (p s) (p (s + 1))) (s : ℕ) : Squarefree (p s) := by
  apply reduced_principal_squarefree (headTailMatrix_hermitian h hA c (s + 1))
    F (p s) (p (s + 1)) hF (hp s) (hp (s + 1))
  · rw [headTailMatrix_prefix]
    exact hfac s
  · exact hfac (s + 1)
  · exact hcop s

theorem headTail_boundary_factor (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) (hc : c ^ 2 = 1)
    (F p0 p1 : Polynomial ℝ)
    (hfac0 : headTailPolynomial h A c 0 = F * p0)
    (hfac1 : headTailPolynomial h A c 1 = F * p1) :
    (A.submatrix Fin.castSucc Fin.castSucc).charpoly = F * (X * p0 - p1) := by
  have h0 : A.charpoly = F * p0 := by
    simpa only [headTailPolynomial, headTailMatrix_zero] using hfac0
  have hb : headTailPolynomial h A c 1 =
      X * A.charpoly - (A.submatrix Fin.castSucc Fin.castSucc).charpoly := by
    unfold headTailPolynomial
    rw [headTailMatrix_succ_border (s := 0), headTailMatrix_zero,
      pathBorder_charpoly]
    simp [hc]
  calc
    _ = X * A.charpoly - headTailPolynomial h A c 1 := by rw [hb]; ring
    _ = F * (X * p0 - p1) := by rw [h0, hfac1]; ring

theorem reduced_headTail_boundary_squarefree (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c : ℝ) (hc : c ^ 2 = 1) (F p0 p1 : Polynomial ℝ)
    (hF : F.Monic) (hp0 : p0.Monic)
    (hfac0 : headTailPolynomial h A c 0 = F * p0)
    (hfac1 : headTailPolynomial h A c 1 = F * p1) (hcop : IsCoprime p0 p1) :
    Squarefree (X * p0 - p1) := by
  have hm := headTail_boundary_factor h A c hc F p0 p1 hfac0 hfac1
  have hmono : (X * p0 - p1).Monic :=
    hF.of_mul_monic_left (hm ▸ Matrix.charpoly_monic _)
  have hcop' : IsCoprime (X * p0 - p1) p0 := by
    have hh := coprime_recurrence_step (p := p1) (q := p0) (L := X)
      (by norm_num : (1 : ℝ) ≠ 0) hcop.symm
    simpa only [C_1, one_mul] using hh.symm
  apply reduced_principal_squarefree hA F (X * p0 - p1) p0 hF hmono hp0 hm
  · simpa only [headTailPolynomial, headTailMatrix_zero] using hfac0
  · exact hcop'

theorem reduced_headTail_exterior_stabilize (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c : ℝ) (hc : c ^ 2 = 1) (F : Polynomial ℝ) (p : ℕ → Polynomial ℝ)
    (hF : F.Monic) (hp : ∀ s, (p s).Monic)
    (hfac : ∀ s, headTailPolynomial h A c s = F * p s) :
    ∃ N C : ℕ, C ≤ 2 * (h + 1) ∧ ∀ s, N ≤ s → exteriorRootCount (p s) = C := by
  obtain ⟨N, C, hC, hstab⟩ := headTail_exterior_stabilize h hA c hc
  refine ⟨N, C - exteriorRootCount F, Nat.le_trans (Nat.sub_le _ _) hC, ?_⟩
  intro s hs
  have hm : exteriorRootCount F + exteriorRootCount (p s) = C := by
    rw [← exteriorRootCount_mul hF.ne_zero (hp s).ne_zero, ← hfac s]
    exact hstab s hs
  omega

end KadarYu
