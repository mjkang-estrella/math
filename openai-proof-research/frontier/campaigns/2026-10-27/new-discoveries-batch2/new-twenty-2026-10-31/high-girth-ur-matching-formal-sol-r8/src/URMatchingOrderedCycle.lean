module
public import URMatchingSurvivorGraph
@[expose] public section
namespace URMatching
open scoped Classical
/-- Every alternating ordered simple cycle in the actual graph occurs in the
existing witness enumeration; colours are extracted from actual edges. -/
theorem ordered_cycle_description {N k : ℕ} (σ : PermutationTuples N 100)
    (hk : 0 < k) (x y : Fin (k+1) ↪ Fin N)
    (ha : ∀ i, (permutationGraph σ).Adj (.inl (x i)) (.inr (y i)))
    (hb : ∀ i, (permutationGraph σ).Adj (.inl (x (i+1))) (.inr (y i))) :
    ∃ w : ValidWitness N k, w.val.1 = x ∧ w.val.2.1 = y ∧ DescriptionOccurs w.val σ := by
  have a : ∀ i, ∃ c, σ c (x i) = y i := ha
  have b : ∀ i, ∃ c, σ c (x (i+1)) = y i := hb
  let w : CycleDescription N k := (x,y,fun i => Classical.choose (a i),
    fun i => Classical.choose (b i))
  refine ⟨⟨w, fun h => False.elim (Nat.ne_of_gt hk h)⟩, rfl, rfl, ?_⟩
  intro i
  exact ⟨Classical.choose_spec (a i), Classical.choose_spec (b i)⟩

/-- Every vertex of every short ordered cycle is actually deleted. -/
theorem ordered_cycle_vertices_removed {N h k : ℕ} (σ : PermutationTuples N 100)
    (hk : 0 < k) (hkh : k < h) (x y : Fin (k+1) ↪ Fin N)
    (ha : ∀ i, (permutationGraph σ).Adj (.inl (x i)) (.inr (y i)))
    (hb : ∀ i, (permutationGraph σ).Adj (.inl (x (i+1))) (.inr (y i)))
    (i : Fin (k+1)) :
    Sum.inl (x i) ∈ removedVertices N h σ ∧ Sum.inr (y i) ∈ removedVertices N h σ := by
  obtain ⟨w,hx,hy,hw⟩ := ordered_cycle_description σ hk x y ha hb
  constructor
  · apply witness_vertex_removed σ w hkh hw
    simp only [witnessVertices, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl ⟨i, by rw [hx]⟩
  · apply witness_vertex_removed σ w hkh hw
    simp only [witnessVertices, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨i, by rw [hy]⟩
end URMatching
