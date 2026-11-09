import TailStabilization

namespace KadarYu

open Matrix Finset Polynomial

noncomputable def rootCountAbove (p : Polynomial ℝ) (c : ℝ) : ℕ := by
  classical
  exact (p.roots.filter fun x => c < x).card

noncomputable def rootCountBelow (p : Polynomial ℝ) (c : ℝ) : ℕ := by
  classical
  exact (p.roots.filter fun x => x < c).card

noncomputable def exteriorRootCount (p : Polynomial ℝ) : ℕ := by
  classical
  exact (p.roots.filter fun x => x ∉ Set.Icc (-2 : ℝ) 2).card

theorem rootCountAbove_charpoly {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (c : ℝ) :
    rootCountAbove A.charpoly c = spectralCountAbove hA c := by
  classical
  unfold rootCountAbove spectralCountAbove
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.filter_map, Multiset.card_map]
  rfl

theorem rootCountBelow_charpoly {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (c : ℝ) :
    rootCountBelow A.charpoly c = spectralCountBelow hA c := by
  classical
  unfold rootCountBelow spectralCountBelow
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.filter_map, Multiset.card_map]
  rfl

theorem exteriorRootCount_eq (p : Polynomial ℝ) :
    exteriorRootCount p = rootCountAbove p 2 + rootCountBelow p (-2) := by
  classical
  have hs : ∀ s : Multiset ℝ,
      (s.filter fun x => x ∉ Set.Icc (-2 : ℝ) 2).card =
        (s.filter fun x => 2 < x).card + (s.filter fun x => x < -2).card := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons x s ih =>
      by_cases hp : 2 < x
      · have hn : ¬ x < -2 := by linarith
        have ho : x ∉ Set.Icc (-2 : ℝ) 2 := fun hx => (not_lt_of_ge hx.2) hp
        rw [Multiset.filter_cons_of_pos (p := fun y : ℝ => y ∉ Set.Icc (-2 : ℝ) 2) s ho, Multiset.filter_cons_of_pos (p := fun y : ℝ => 2 < y) s hp,
          Multiset.filter_cons_of_neg (p := fun y : ℝ => y < -2) s hn]
        simp only [Multiset.card_cons]
        omega
      · by_cases hn : x < -2
        · have ho : x ∉ Set.Icc (-2 : ℝ) 2 := fun hx => (not_lt_of_ge hx.1) hn
          rw [Multiset.filter_cons_of_pos (p := fun y : ℝ => y ∉ Set.Icc (-2 : ℝ) 2) s ho, Multiset.filter_cons_of_neg (p := fun y : ℝ => 2 < y) s hp,
            Multiset.filter_cons_of_pos (p := fun y : ℝ => y < -2) s hn]
          simp only [Multiset.card_cons]
          omega
        · have hi : x ∈ Set.Icc (-2 : ℝ) 2 := ⟨le_of_not_gt hn, le_of_not_gt hp⟩
          rw [Multiset.filter_cons_of_neg (p := fun y : ℝ => y ∉ Set.Icc (-2 : ℝ) 2) s (not_not.mpr hi),
            Multiset.filter_cons_of_neg (p := fun y : ℝ => 2 < y) s hp, Multiset.filter_cons_of_neg (p := fun y : ℝ => y < -2) s hn]
          exact ih
  exact hs p.roots

theorem jacobi_exterior_roots_stabilize (r : ℕ) (diag off : ℕ → ℝ)
    (hd : ∀ i, r ≤ i → diag i = 0) (ho : ∀ i, r ≤ i → off i = 1) :
    ∃ N C : ℕ, C ≤ 2 * r ∧ ∀ s, N ≤ s →
      exteriorRootCount (jacobiPolynomial diag off (r + s)) = C := by
  obtain ⟨N, a, b, ha, hb, hstab⟩ := jacobi_exterior_counts_stabilize r diag off hd ho
  refine ⟨N, a + b, by omega, ?_⟩
  intro s hs
  rw [exteriorRootCount_eq, jacobiPolynomial,
    rootCountAbove_charpoly (jacobiMatrix_hermitian (r + s) diag off),
    rootCountBelow_charpoly (jacobiMatrix_hermitian (r + s) diag off),
    (hstab s hs).1, (hstab s hs).2]

end KadarYu
