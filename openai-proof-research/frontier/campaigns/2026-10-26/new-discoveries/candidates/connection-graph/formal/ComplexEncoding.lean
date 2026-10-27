import GraphComplex

open Finset Matrix

namespace ConnectionGraph
noncomputable section
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The canonical ordered edges of a finite family of singleton/pair faces. -/
def complexEdges (F : Finset (Finset V)) : Finset (V × V) :=
  univ.filter fun e => e.1 < e.2 ∧ {e.1, e.2} ∈ F

theorem complexEdges_valid (F : Finset (Finset V)) : ValidEdges (complexEdges F) := by
  intro e he
  exact (mem_filter.mp he).2.1

theorem graphFaces_complexEdges (F : Finset (Finset V))
    (hsingle : ∀ v : V, {v} ∈ F)
    (hcard : ∀ s ∈ F, s.card = 1 ∨ s.card = 2) :
    graphFaces (complexEdges F) = F := by
  ext s
  constructor
  · intro hs
    obtain ⟨i, _, rfl⟩ := mem_image.mp hs
    cases i with
    | inl v => exact hsingle v
    | inr e => exact (mem_filter.mp e.property).2.2
  · intro hs
    rcases hcard s hs with h1 | h2
    · obtain ⟨v, rfl⟩ := card_eq_one.mp h1
      exact singleton_mem_graphFaces _ v
    · obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp h2
      rcases lt_or_gt_of_ne hab with hab' | hba'
      · have he : (a, b) ∈ complexEdges F := mem_filter.mpr ⟨mem_univ _, hab', hs⟩
        exact simplex_mem_graphFaces _ (Sum.inr ⟨(a, b), he⟩)
      · have he : (b, a) ∈ complexEdges F :=
          mem_filter.mpr ⟨mem_univ _, hba', by simpa [pair_comm] using hs⟩
        simpa only [simplex, pair_comm b a] using
          simplex_mem_graphFaces _ (Sum.inr ⟨(b, a), he⟩)

theorem complexEncoding_card (F : Finset (Finset V))
    (hsingle : ∀ v : V, {v} ∈ F)
    (hcard : ∀ s ∈ F, s.card = 1 ∨ s.card = 2) :
    F.card = Fintype.card V + (complexEdges F).card := by
  calc
    F.card = (graphFaces (complexEdges F)).card :=
      congrArg Finset.card (graphFaces_complexEdges F hsingle hcard).symm
    _ = _ := graphFaces_card (complexEdges_valid F)

end
end ConnectionGraph
