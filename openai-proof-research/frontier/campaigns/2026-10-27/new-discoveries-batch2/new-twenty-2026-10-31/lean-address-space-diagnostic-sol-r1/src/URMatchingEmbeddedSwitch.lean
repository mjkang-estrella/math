module
public import URMatchingBase
@[expose] public section
namespace URMatching
universe u v
variable {I : Type u} {V : Type v} [Fintype I] [DecidableEq V]

def indexedEdges (e : Sum I I ↪ V) (σ : Equiv.Perm I) : Finset (Sym2 V) :=
  Finset.univ.image (fun i => s(e (Sum.inl i), e (Sum.inr (σ i))))

theorem indexedEdges_matching (G : SimpleGraph V) (e : Sum I I ↪ V) (σ : Equiv.Perm I)
    (h : ∀ i, G.Adj (e (Sum.inl i)) (e (Sum.inr (σ i)))) :
    IsMatching G (indexedEdges e σ) := by
  constructor
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact h i
  · intro a ha b hb w hwa hwb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    simp only [Sym2.mem_iff] at hwa hwb
    have hij : i = j := by
      rcases hwa with hi | hi <;> rcases hwb with hj | hj
      · exact Sum.inl.inj (e.injective (hi.symm.trans hj))
      · cases e.injective (hi.symm.trans hj)
      · cases e.injective (hi.symm.trans hj)
      · exact σ.injective (Sum.inr.inj (e.injective (hi.symm.trans hj)))
    subst j
    rfl

theorem indexedEdges_covered (e : Sum I I ↪ V) (σ : Equiv.Perm I) :
    Covered (indexedEdges e σ) = Set.range e := by
  ext w
  constructor
  · rintro ⟨a, ha, hw⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    rcases Sym2.mem_iff.mp hw with hw | hw
    · exact ⟨Sum.inl i, hw.symm⟩
    · exact ⟨Sum.inr (σ i), hw.symm⟩
  · rintro ⟨z, rfl⟩
    cases z with
    | inl i => exact ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, by simp⟩
    | inr j => exact ⟨_, Finset.mem_image.mpr ⟨σ.symm j, Finset.mem_univ _, rfl⟩, by simp⟩

theorem indexedEdges_injective (e : Sum I I ↪ V) :
    Function.Injective (indexedEdges e) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hi : s(e (Sum.inl i), e (Sum.inr (σ i))) ∈ indexedEdges e τ := by
    rw [← h]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
  have hm : e (Sum.inl i) ∈ s(e (Sum.inl j), e (Sum.inr (τ j))) := by rw [hj]; simp
  have hij : i = j := by
    rcases Sym2.mem_iff.mp hm with hm | hm
    · exact Sum.inl.inj (e.injective hm)
    · cases e.injective hm
  subst j
  have hr : e (Sum.inr (σ i)) ∈ s(e (Sum.inl i), e (Sum.inr (τ i))) := by rw [hj]; simp
  rcases Sym2.mem_iff.mp hr with hr | hr
  · cases e.injective hr
  · exact Sum.inr.inj (e.injective hr)

/-- Switching works for partial matchings in arbitrary finite graphs: vertices outside
range e are uncovered before and after. The permutation may fix any complement. -/
theorem indexed_switch_not_ur (G : SimpleGraph V) (e : Sum I I ↪ V)
    (σ : Equiv.Perm I) (hσ : σ ≠ Equiv.refl I)
    (cross : ∀ i, G.Adj (e (Sum.inl i)) (e (Sum.inr (σ i)))) :
    ¬ IsUR G (indexedEdges e (Equiv.refl I)) := by
  intro H
  have he := H.2 (indexedEdges e σ) (indexedEdges_matching G e σ cross)
    (by rw [indexedEdges_covered, indexedEdges_covered])
  exact hσ (indexedEdges_injective e he)
end URMatching
