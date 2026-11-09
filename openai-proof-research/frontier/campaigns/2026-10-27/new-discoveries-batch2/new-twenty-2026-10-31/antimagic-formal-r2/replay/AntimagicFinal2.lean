import Antimagic2Binary
namespace Antimagic.Round2

/-- The exact construction cases still open after the depth-one and binary depth-two proofs. -/
def RemainingConstruction : Prop := ∀ t n, 2 ≤ t → Even t → 2 ≤ n → ¬ (t = 2 ∧ n = 2) →
  ∃ (f : Labeling (tree t n)),
    (∀ (u v : Vertex t n) (h : Child u v),
      (f ⟨s(u, v), (tree t n).mem_edgeSet.mpr (Or.inl h)⟩).val + 1 =
        label t n v.1.val v.2.val) ∧
    IsLocal (tree t n) f ∧ colorCount (tree t n) f = t ^ n + 1

theorem construction_of_higher (higher : RemainingConstruction) : Construction := by
  intro t n ht he hn
  by_cases h : n = 1
  · subst n
    exact star_construction t ht
  · by_cases hb : t = 2 ∧ n = 2
    · obtain ⟨rfl, rfl⟩ := hb
      exact binary_construction
    · exact higher t n ht he (by omega) hb

/-- Conditional only on the still-open depth-at-least-two construction. -/
theorem even_case (higher : RemainingConstruction)
    (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) :
    IsLeast (spectrum (tree t n)) (t ^ n + 1) :=
  Antimagic.even_case lowerBound (construction_of_higher higher) t n ht he hn

/-- The model endpoint is unconditional at depth one, without an evenness restriction. -/
theorem depth_one (t : ℕ) (ht : 2 ≤ t) :
    IsLeast (spectrum (tree t 1)) (t + 1) := by
  obtain ⟨f, _, hf, hc⟩ := star_construction t ht
  simpa only [pow_one] using least_of_bounds (tree t 1) (t ^ 1 + 1)
    ⟨f, hf, hc⟩ (lowerBound t 1 ht (by omega))

theorem binary_depth_two : IsLeast (spectrum (tree 2 2)) 5 := by
  obtain ⟨f, _, hf, hc⟩ := binary_construction
  exact least_of_bounds _ _ ⟨f, hf, hc⟩ (lowerBound 2 2 (by decide) (by decide))

/-- Conditional on precisely the higher construction and arbitrary-tree bridge. -/
theorem mathdb_354228 (higher : RemainingConstruction) (bridge : ModelBridge)
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n)
    (full : FullTree G t n) :
    IsLeast (spectrum G) (numLeaves G + 1) ∧ chiLA G = numLeaves G + 1 :=
  Antimagic.mathdb_354228 lowerBound (construction_of_higher higher) bridge modelLeaves
    G t n ht he hn full

#print axioms construction_of_higher
#print axioms even_case
#print axioms depth_one
#print axioms binary_depth_two
#print axioms mathdb_354228
end Antimagic.Round2
