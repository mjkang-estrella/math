import HeadTailSpectral

namespace KadarYu

open Matrix Finset Polynomial

theorem closed_band_closure_of_interval_hits (S : Set ℝ)
    (hhit : ∀ a b : ℝ, -2 < a → b < 2 → a < b → ∃ y ∈ S, a < y ∧ y < b) :
    Set.Icc (-2 : ℝ) 2 ⊆ closure S := by
  have hIoo : Set.Ioo (-2 : ℝ) 2 ⊆ closure S := by
    intro x hx
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let δ := min ε (min (x + 2) (2 - x)) / 2
    have hmin : 0 < min ε (min (x + 2) (2 - x)) :=
      lt_min hε (lt_min (by linarith [hx.1]) (by linarith [hx.2]))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδε : δ ≤ ε / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hδl : δ ≤ (x + 2) / 2 :=
      div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
    have hδr : δ ≤ (2 - x) / 2 :=
      div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
    have ha : -2 < x - δ := by linarith [hx.1]
    have hb : x + δ < 2 := by linarith [hx.2]
    obtain ⟨y, hyS, hy1, hy2⟩ := hhit (x - δ) (x + δ) ha hb (by linarith)
    refine ⟨y, hyS, ?_⟩
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith
  have hh := closure_minimal hIoo isClosed_closure
  rw [closure_Ioo (by norm_num : (-2 : ℝ) ≠ 2)] at hh
  exact hh

theorem headTail_roots_hit_interval (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c : ℝ) (hc : c ^ 2 = 1)
    (a b : ℝ) (ha : -2 < a) (hb : b < 2) (hab : a < b) :
    ∃ s : ℕ, ∃ x : ℝ, a < x ∧ x < b ∧ (headTailPolynomial h A c s).eval x = 0 := by
  let B := (a + b) / 2
  have haB : a < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  obtain ⟨s, f, hf⟩ := exists_many_path_roots a B ha (hBb.trans hb) haB (h + 2)
  let hM := headTailMatrix_hermitian h hA c s
  let hS := hM.submatrix (headTailSplitEquiv h s)
  let hT := hS.submatrix Sum.inr
  let hP := jacobiMatrix_hermitian s (fun _ => 0) (fun _ => c)
  have htail := headTail_tail_equiv h A c s
  have hlo : spectralCountAbove hP a ≤ spectralCountAbove hM a := by
    have hh := (spectralCountAbove_submatrix_inr hS a).trans_eq
      (spectralCountAbove_submatrix_equiv (headTailSplitEquiv h s) hM a)
    exact (spectralCountAbove_congr hT hP htail a).symm.trans_le hh
  have hhi : spectralCountAbove hM B ≤ (h + 1) + spectralCountAbove hP B := by
    calc
      _ = spectralCountAbove hS B :=
        (spectralCountAbove_submatrix_equiv (headTailSplitEquiv h s) hM B).symm
      _ ≤ Fintype.card (Fin (h + 1)) + spectralCountAbove hT B :=
        spectralCountAbove_le_head_add_tail hS B
      _ = _ := by rw [spectralCountAbove_congr hT hP htail B]; simp
  have hmany : h + 2 ≤ spectralCountInterval hP a B := by
    apply spectralCountInterval_le_of_roots hP a B (h + 2) f
    intro i
    refine ⟨?_, (hf i).2.1, (hf i).2.2.le⟩
    change (jacobiPolynomial (fun _ => 0) (fun _ => c) s).eval (f i) = 0
    rw [unitSquaredPath_polynomial c hc]
    exact (hf i).1
  have hpartition := spectralCountAbove_partition hP a B haB
  have hcount : spectralCountAbove hM B < spectralCountAbove hM a := by omega
  obtain ⟨i, hi, hiB⟩ := exists_eigenvalue_interval_of_count_lt hM a B hcount
  refine ⟨s, hM.eigenvalues i, hi, hiB.trans_lt hBb, ?_⟩
  have hm : hM.eigenvalues i ∈ (headTailMatrix h A c s).charpoly.roots := by
    rw [hM.roots_charpoly_eq_eigenvalues]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hm

theorem headTail_roots_dense_closed_band (h : ℕ)
    {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hA : A.IsHermitian)
    (c : ℝ) (hc : c ^ 2 = 1) :
    Set.Icc (-2 : ℝ) 2 ⊆ closure
      {y : ℝ | y ∈ Set.Icc (-2 : ℝ) 2 ∧ ∃ s : ℕ, (headTailPolynomial h A c s).eval y = 0} := by
  apply closed_band_closure_of_interval_hits
  intro a b ha hb hab
  obtain ⟨s, y, hy1, hy2, hyr⟩ := headTail_roots_hit_interval h hA c hc a b ha hb hab
  exact ⟨y, ⟨⟨(ha.trans hy1).le, (hy2.trans hb).le⟩, ⟨s, hyr⟩⟩, hy1, hy2⟩

end KadarYu
