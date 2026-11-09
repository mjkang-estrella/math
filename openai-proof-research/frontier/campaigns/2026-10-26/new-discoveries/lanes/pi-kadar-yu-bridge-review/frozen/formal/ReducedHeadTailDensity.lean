import ReducedHeadTail

namespace KadarYu

open Matrix Finset Polynomial

noncomputable def rootCountInterval (p : Polynomial ℝ) (a b : ℝ) : ℕ := by
  classical
  exact (p.roots.filter fun x => a < x ∧ x ≤ b).card

theorem rootCountInterval_charpoly {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (a b : ℝ) :
    rootCountInterval A.charpoly a b = spectralCountInterval hA a b := by
  classical
  unfold rootCountInterval spectralCountInterval
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.filter_map, Multiset.card_map]
  rfl

theorem rootCountInterval_mul {F p : Polynomial ℝ} (hF : F ≠ 0) (hp : p ≠ 0)
    (a b : ℝ) :
    rootCountInterval (F * p) a b = rootCountInterval F a b + rootCountInterval p a b := by
  classical
  simp only [rootCountInterval, Polynomial.roots_mul (mul_ne_zero hF hp),
    Multiset.filter_add, Multiset.card_add]

theorem rootCountInterval_le_card (F : Polynomial ℝ) (a b : ℝ) :
    rootCountInterval F a b ≤ F.roots.card := by
  classical
  exact Multiset.card_le_card (Multiset.filter_le _ _)

theorem headTail_many_interval (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c : ℝ) (hc : c ^ 2 = 1)
    (a b : ℝ) (ha : -2 < a) (hb : b < 2) (hab : a < b) (R : ℕ) :
    ∃ s, R ≤ spectralCountInterval (headTailMatrix_hermitian h hA c s) a b := by
  obtain ⟨s, f, hf⟩ := exists_many_path_roots a b ha hb hab (R + h + 1)
  let hM := headTailMatrix_hermitian h hA c s
  let hS := hM.submatrix (headTailSplitEquiv h s)
  let hT := hS.submatrix Sum.inr
  let hP := jacobiMatrix_hermitian s (fun _ => 0) (fun _ => c)
  have htail := headTail_tail_equiv h A c s
  have hlo : spectralCountAbove hP a ≤ spectralCountAbove hM a := by
    have hh := (spectralCountAbove_submatrix_inr hS a).trans_eq
      (spectralCountAbove_submatrix_equiv (headTailSplitEquiv h s) hM a)
    exact (spectralCountAbove_congr hT hP htail a).symm.trans_le hh
  have hhi : spectralCountAbove hM b ≤ (h + 1) + spectralCountAbove hP b := by
    calc
      _ = spectralCountAbove hS b :=
        (spectralCountAbove_submatrix_equiv (headTailSplitEquiv h s) hM b).symm
      _ ≤ Fintype.card (Fin (h + 1)) + spectralCountAbove hT b :=
        spectralCountAbove_le_head_add_tail hS b
      _ = _ := by rw [spectralCountAbove_congr hT hP htail b]; simp
  have hmany : R + h + 1 ≤ spectralCountInterval hP a b := by
    apply spectralCountInterval_le_of_roots hP a b (R + h + 1) f
    intro i
    refine ⟨?_, (hf i).2.1, (hf i).2.2.le⟩
    change (jacobiPolynomial (fun _ => 0) (fun _ => c) s).eval (f i) = 0
    rw [unitSquaredPath_polynomial c hc]
    exact (hf i).1
  have hpartition := spectralCountAbove_partition hP a b hab
  have hpartitionM := spectralCountAbove_partition hM a b hab
  exact ⟨s, by omega⟩

theorem reduced_headTail_roots_hit_interval (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c : ℝ) (hc : c ^ 2 = 1) (F : Polynomial ℝ) (p : ℕ → Polynomial ℝ)
    (hF : F.Monic) (hp : ∀ s, (p s).Monic)
    (hfac : ∀ s, headTailPolynomial h A c s = F * p s)
    (a b : ℝ) (ha : -2 < a) (hb : b < 2) (hab : a < b) :
    ∃ s : ℕ, ∃ x : ℝ, a < x ∧ x < b ∧ (p s).eval x = 0 := by
  let B := (a + b) / 2
  have haB : a < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  obtain ⟨s, hs⟩ := headTail_many_interval h hA c hc a B ha (hBb.trans hb) haB
    (F.roots.card + 1)
  have heq : rootCountInterval F a B + rootCountInterval (p s) a B =
      spectralCountInterval (headTailMatrix_hermitian h hA c s) a B := by
    rw [← rootCountInterval_mul hF.ne_zero (hp s).ne_zero, ← hfac s]
    exact rootCountInterval_charpoly (headTailMatrix_hermitian h hA c s) a B
  have hbound := rootCountInterval_le_card F a B
  have hpos : 0 < rootCountInterval (p s) a B := by omega
  change 0 < ((p s).roots.filter fun x => a < x ∧ x ≤ B).card at hpos
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  obtain ⟨hxroot, hxa, hxB⟩ := Multiset.mem_filter.mp hx
  exact ⟨s, x, hxa, hxB.trans_lt hBb, (Polynomial.mem_roots (hp s).ne_zero).mp hxroot⟩

theorem reduced_headTail_roots_dense_closed_band (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c : ℝ) (hc : c ^ 2 = 1) (F : Polynomial ℝ) (p : ℕ → Polynomial ℝ)
    (hF : F.Monic) (hp : ∀ s, (p s).Monic)
    (hfac : ∀ s, headTailPolynomial h A c s = F * p s) :
    Set.Icc (-2 : ℝ) 2 ⊆ closure
      {y : ℝ | y ∈ Set.Icc (-2 : ℝ) 2 ∧ ∃ s : ℕ, (p s).eval y = 0} := by
  apply closed_band_closure_of_interval_hits
  intro a b ha hb hab
  obtain ⟨s, y, hy1, hy2, hyr⟩ := reduced_headTail_roots_hit_interval h hA c hc F p
    hF hp hfac a b ha hb hab
  exact ⟨y, ⟨⟨(ha.trans hy1).le, (hy2.trans hb).le⟩, ⟨s, hyr⟩⟩, hy1, hy2⟩

theorem reduced_headTail_root_distribution (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c : ℝ) (hc : c ^ 2 = 1) (F : Polynomial ℝ) (p : ℕ → Polynomial ℝ)
    (hF : F.Monic) (hp : ∀ s, (p s).Monic)
    (hfac : ∀ s, headTailPolynomial h A c s = F * p s)
    (hcop : ∀ s, IsCoprime (p s) (p (s + 1))) :
    Squarefree (X * p 0 - p 1) ∧ (∀ s, Squarefree (p s)) ∧
    (∃ N C : ℕ, C ≤ 2 * (h + 1) ∧ ∀ s, N ≤ s → exteriorRootCount (p s) = C) ∧
    Set.Icc (-2 : ℝ) 2 ⊆ closure
      {y : ℝ | y ∈ Set.Icc (-2 : ℝ) 2 ∧ ∃ s : ℕ, (p s).eval y = 0} :=
  ⟨reduced_headTail_boundary_squarefree h hA c hc F (p 0) (p 1) hF (hp 0)
      (hfac 0) (hfac 1) (hcop 0),
    reduced_headTail_squarefree h hA c F p hF hp hfac hcop,
    reduced_headTail_exterior_stabilize h hA c hc F p hF hp hfac,
    reduced_headTail_roots_dense_closed_band h hA c hc F p hF hp hfac⟩

end KadarYu
