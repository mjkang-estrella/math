import PathGrid

namespace KadarYu

open Matrix Finset Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def spectralCountInterval {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (a b : ℝ) : ℕ := by
  classical
  exact (univ.filter fun i => a < hA.eigenvalues i ∧ hA.eigenvalues i ≤ b).card

theorem spectralCountAbove_partition {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (a b : ℝ) (hab : a < b) :
    spectralCountAbove hA b + spectralCountInterval hA a b = spectralCountAbove hA a := by
  classical
  let S := univ.filter fun i => a < hA.eigenvalues i
  have h := card_filter_add_card_filter_not (s := S) (fun i => b < hA.eigenvalues i)
  have h1 : S.filter (fun i => b < hA.eigenvalues i) =
      univ.filter (fun i => b < hA.eigenvalues i) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, S]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨hab.trans h, h⟩
  have h2 : S.filter (fun i => ¬ b < hA.eigenvalues i) =
      univ.filter (fun i => a < hA.eigenvalues i ∧ hA.eigenvalues i ≤ b) := by
    ext i
    simp [S, not_lt]
  rw [h1, h2] at h
  exact h

theorem spectralCountInterval_le_of_roots {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (a b : ℝ) (R : ℕ) (f : Fin R ↪ ℝ)
    (hf : ∀ i, A.charpoly.eval (f i) = 0 ∧ a < f i ∧ f i ≤ b) :
    R ≤ spectralCountInterval hA a b := by
  classical
  have hex : ∀ i, ∃ j, hA.eigenvalues j = f i := by
    intro i
    have hm := (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mpr (hf i).1
    rw [hA.roots_charpoly_eq_eigenvalues] at hm
    obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hm
    exact ⟨j, hj⟩
  choose j hj using hex
  let S := univ.filter fun k => a < hA.eigenvalues k ∧ hA.eigenvalues k ≤ b
  let g : Fin R → S := fun i => ⟨j i, mem_filter.mpr ⟨mem_univ _, by rw [hj i]; exact (hf i).2⟩⟩
  have hg : Function.Injective g := by
    intro i k h
    apply f.injective
    rw [← hj i, ← hj k]
    exact congrArg hA.eigenvalues (congrArg Subtype.val h)
  have h := Fintype.card_le_of_injective g hg
  change R ≤ S.card
  simpa only [Fintype.card_fin, Fintype.card_coe] using h

theorem exists_eigenvalue_interval_of_count_lt {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (a b : ℝ)
    (h : spectralCountAbove hA b < spectralCountAbove hA a) :
    ∃ i, a < hA.eigenvalues i ∧ hA.eigenvalues i ≤ b := by
  classical
  by_contra hn
  push Not at hn
  have hs : (univ.filter fun i => a < hA.eigenvalues i) ⊆
      (univ.filter fun i => b < hA.eigenvalues i) := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, hn i (mem_filter.mp hi).2⟩
  exact (not_lt_of_ge (card_le_card hs)) h

theorem jacobi_roots_hit_interval (r : ℕ) (diag off : ℕ → ℝ)
    (hd : ∀ i, r ≤ i → diag i = 0) (ho : ∀ i, r ≤ i → off i = 1)
    (a b : ℝ) (ha : -2 < a) (hb : b < 2) (hab : a < b) :
    ∃ s : ℕ, ∃ x : ℝ, a < x ∧ x < b ∧
      (jacobiPolynomial diag off (r + s)).eval x = 0 := by
  let B := (a + b) / 2
  have haB : a < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  obtain ⟨s, f, hf⟩ := exists_many_path_roots a B ha (hBb.trans hb) haB (r + 1)
  let hA := jacobiMatrix_hermitian (r + s) diag off
  let hS := hA.submatrix (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s))
  let hT := hS.submatrix Sum.inr
  let hP := jacobiMatrix_hermitian s (fun _ => 0) (fun _ => 1)
  have htail := jacobiMatrix_tail_block r s diag off hd ho
  have hlo : spectralCountAbove hP a ≤ spectralCountAbove hA a := by
    have h := spectralCountAbove_submatrix_inr hS a
    have hh := h.trans_eq (spectralCountAbove_submatrix_equiv finSumFinEquiv hA a)
    exact (spectralCountAbove_congr hT hP htail a).symm.trans_le hh
  have hhi : spectralCountAbove hA B ≤ r + spectralCountAbove hP B := by
    calc
      _ = spectralCountAbove hS B :=
        (spectralCountAbove_submatrix_equiv finSumFinEquiv hA B).symm
      _ ≤ Fintype.card (Fin r) + spectralCountAbove hT B :=
        spectralCountAbove_le_head_add_tail hS B
      _ = r + spectralCountAbove hP B := by
        rw [spectralCountAbove_congr hT hP htail B]
        simp
  have hmany : r + 1 ≤ spectralCountInterval hP a B :=
    spectralCountInterval_le_of_roots hP a B (r + 1) f
      (fun i => ⟨(hf i).1, (hf i).2.1, (hf i).2.2.le⟩)
  have hpartition := spectralCountAbove_partition hP a B haB
  have hcount : spectralCountAbove hA B < spectralCountAbove hA a := by omega
  obtain ⟨i, hi, hiB⟩ := exists_eigenvalue_interval_of_count_lt hA a B hcount
  refine ⟨s, hA.eigenvalues i, hi, hiB.trans_lt hBb, ?_⟩
  have hm : hA.eigenvalues i ∈ (jacobiMatrix (r + s) diag off).charpoly.roots := by
    rw [hA.roots_charpoly_eq_eigenvalues]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hm

theorem jacobi_roots_dense_closed_band (r : ℕ) (diag off : ℕ → ℝ)
    (hd : ∀ i, r ≤ i → diag i = 0) (ho : ∀ i, r ≤ i → off i = 1) :
    Set.Icc (-2 : ℝ) 2 ⊆ closure
      {y : ℝ | y ∈ Set.Icc (-2 : ℝ) 2 ∧
        ∃ s : ℕ, (jacobiPolynomial diag off (r + s)).eval y = 0} := by
  let S := {y : ℝ | y ∈ Set.Icc (-2 : ℝ) 2 ∧
    ∃ s : ℕ, (jacobiPolynomial diag off (r + s)).eval y = 0}
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
    obtain ⟨s, y, hy1, hy2, hyr⟩ := jacobi_roots_hit_interval r diag off hd ho
      (x - δ) (x + δ) ha hb (by linarith)
    refine ⟨y, ⟨⟨by linarith, by linarith⟩, ⟨s, hyr⟩⟩, ?_⟩
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith
  have h := closure_minimal hIoo isClosed_closure
  rw [closure_Ioo (by norm_num : (-2 : ℝ) ≠ 2)] at h
  exact h

theorem jacobi_root_distribution (r : ℕ) (diag off : ℕ → ℝ)
    (hoff : ∀ i, off i ≠ 0)
    (hd : ∀ i, r ≤ i → diag i = 0) (ho : ∀ i, r ≤ i → off i = 1) :
    (∀ n, Squarefree (jacobiPolynomial diag off n)) ∧
    (∃ N C : ℕ, C ≤ 2 * r ∧ ∀ s, N ≤ s →
      exteriorRootCount (jacobiPolynomial diag off (r + s)) = C) ∧
    Set.Icc (-2 : ℝ) 2 ⊆ closure
      {y : ℝ | y ∈ Set.Icc (-2 : ℝ) 2 ∧
        ∃ s : ℕ, (jacobiPolynomial diag off (r + s)).eval y = 0} :=
  ⟨fun n => jacobiPolynomial_squarefree diag off hoff n,
    jacobi_exterior_roots_stabilize r diag off hd ho,
    jacobi_roots_dense_closed_band r diag off hd ho⟩

end KadarYu
