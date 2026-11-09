module
public import URMatchingBase
@[expose] public section
namespace URMatching
variable {I : Type} [Fintype I] [DecidableEq I]
/-- Actual unordered edges on disjoint left and right copies of the index set. -/
def permutationEdges (σ : Equiv.Perm I) : Finset (Sym2 (Sum I I)) :=
  Finset.univ.image (fun i => s(Sum.inl i, Sum.inr (σ i)))

theorem permutationEdges_matching (G : SimpleGraph (Sum I I)) (σ : Equiv.Perm I)
    (h : ∀ i, G.Adj (Sum.inl i) (Sum.inr (σ i))) :
    IsMatching G (permutationEdges σ) := by
  constructor
  · intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact h i
  · intro e he f hf v hve hvf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hf
    have hij : i = j := by
      cases v with
      | inl k =>
        simp only [Sym2.mem_iff, Sum.inl.injEq, Sum.inl_ne_inr, or_false] at hve hvf
        exact hve.symm.trans hvf
      | inr k =>
        simp only [Sym2.mem_iff, Sum.inr.injEq, Sum.inr_ne_inl, false_or] at hve hvf
        exact σ.injective (hve.symm.trans hvf)
    subst j
    rfl

theorem permutationEdges_covered (σ : Equiv.Perm I) :
    Covered (permutationEdges σ) = Set.univ := by
  ext v
  simp only [Set.mem_univ, iff_true]
  cases v with
  | inl i => exact ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, by simp⟩
  | inr j => exact ⟨_, Finset.mem_image.mpr ⟨σ.symm j, Finset.mem_univ _, rfl⟩, by simp⟩

theorem permutationEdges_injective :
    Function.Injective (permutationEdges (I := I)) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hi : s(Sum.inl i, Sum.inr (σ i)) ∈ permutationEdges τ := by
    rw [← h]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
  have hm : Sum.inl i ∈ s(Sum.inl j, Sum.inr (τ j)) := by rw [hj]; simp
  have hij : i = j := by simpa using hm
  subst j
  have hr : Sum.inr (σ i) ∈ s(Sum.inl i, Sum.inr (τ i)) := by rw [hj]; simp
  simpa using hr

/-- A nonidentity switch gives a distinct matching with exactly the same covered vertices.
No UR, DAG, expansion, or probabilistic property is built into the representation. -/
theorem permutation_switch_not_ur (G : SimpleGraph (Sum I I)) (σ : Equiv.Perm I)
    (hσ : σ ≠ Equiv.refl I)
    (cross : ∀ i, G.Adj (Sum.inl i) (Sum.inr (σ i))) :
    ¬ IsUR G (permutationEdges (Equiv.refl I)) := by
  intro H
  have he := H.2 (permutationEdges σ) (permutationEdges_matching G σ cross)
    (by rw [permutationEdges_covered, permutationEdges_covered])
  exact hσ (permutationEdges_injective he)
end URMatching
