module
public import URMatchingSurvivorDegree
public import URMatchingSurvivingColours
@[expose] public section
namespace URMatching
open scoped Classical
def LeftSurvivor {N : ℕ} {h : ℕ} {σ : PermutationTuples N 100} (v : Survivor h σ) : Prop :=
  ∃ x, v.val = Sum.inl x

theorem survivor_bipartite {N h : ℕ} (σ : PermutationTuples N 100)
    (u v : Survivor h σ) (huv : (survivorGraph h σ).Adj u v) :
    (LeftSurvivor u ∧ ¬ LeftSurvivor v) ∨ (¬ LeftSurvivor u ∧ LeftSurvivor v) := by
  obtain ⟨u,hu⟩ := u
  obtain ⟨v,hv⟩ := v
  cases u <;> cases v <;> simp_all [LeftSurvivor, survivorGraph, inducedGraph, permutationGraph, permutationAdj]

def SurvivorNoHole {N : ℕ} (h a : ℕ) (σ : PermutationTuples N 100) : Prop :=
  ∀ A B : Finset (Fin N), A.card = a → B.card = a →
    (∀ x ∈ A, Sum.inl x ∉ removedVertices N h σ) →
    (∀ y ∈ B, Sum.inr y ∉ removedVertices N h σ) →
    ∃ u v : Survivor h σ, (∃ x ∈ A, u.val = Sum.inl x) ∧
      (∃ y ∈ B, v.val = Sum.inr y) ∧ (survivorGraph h σ).Adj u v

theorem induced_no_hole {N h a : ℕ} (σ : PermutationTuples N 100)
    (hh : ∀ A B : Finset (Fin N), A.card = a → B.card = a → ∃ c, ∃ x ∈ A, σ c x ∈ B) :
    SurvivorNoHole h a σ := by
  intro A B hA hB hleft hright
  obtain ⟨c,x,hx,hy⟩ := hh A B hA hB
  exact ⟨⟨Sum.inl x,hleft x hx⟩, ⟨Sum.inr (σ c x),hright _ hy⟩,
    ⟨x,hx,rfl⟩,⟨σ c x,hy,rfl⟩,c,rfl⟩

theorem exists_induced_survivor (h : ℕ) : ∃ a : ℕ, 0 < a ∧ h ≤ a ∧
    ∃ σ : PermutationTuples (4*a) 100,
      100*(removedVertices (4*a) h σ).card < 4*a ∧
      DegreeBound (survivorGraph h σ) 100 ∧ SurvivorNoHole h a σ := by
  obtain ⟨a,ha,hh,σ,hs,hn⟩ := exists_sparse_deletion_tuple h
  exact ⟨a,ha,hh,σ,hs,survivor_degree_bound h σ,induced_no_hole σ hn⟩
end URMatching
