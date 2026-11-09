module
public import URMatchingJointTuple
@[expose] public section
namespace URMatching
open scoped Classical
abbrev BipartiteVertex (N : ℕ) := Sum (Fin N) (Fin N)
noncomputable def witnessVertices {N k : ℕ} (w : CycleDescription N k) : Finset (BipartiteVertex N) :=
  Finset.univ.image (fun i => Sum.inl (w.1 i)) ∪ Finset.univ.image (fun i => Sum.inr (w.2.1 i))

theorem witness_vertices_bound {N k : ℕ} (w : CycleDescription N k) :
    (witnessVertices w).card ≤ 2*(k+1) := by
  have hx := Finset.card_image_le (s := (Finset.univ : Finset (Fin (k+1)))) (f := fun i => (Sum.inl (w.1 i) : BipartiteVertex N))
  have hy := Finset.card_image_le (s := (Finset.univ : Finset (Fin (k+1)))) (f := fun i => (Sum.inr (w.2.1 i) : BipartiteVertex N))
  have hu := Finset.card_union_le (Finset.univ.image (fun i => (Sum.inl (w.1 i) : BipartiteVertex N)))
    (Finset.univ.image (fun i => (Sum.inr (w.2.1 i) : BipartiteVertex N)))
  simp only [Finset.card_univ, Fintype.card_fin] at hx hy
  unfold witnessVertices
  omega

noncomputable def occurringWitnesses (N k : ℕ) (σ : PermutationTuples N 100) : Finset (ValidWitness N k) :=
  Finset.univ.filter fun w => DescriptionOccurs w.val σ
noncomputable def removedAt (N k : ℕ) (σ : PermutationTuples N 100) : Finset (BipartiteVertex N) :=
  (occurringWitnesses N k σ).biUnion fun w => witnessVertices w.val
noncomputable def removedVertices (N h : ℕ) (σ : PermutationTuples N 100) : Finset (BipartiteVertex N) :=
  (Finset.range h).biUnion fun k => removedAt N k σ

theorem removedAt_bound (N k : ℕ) (σ : PermutationTuples N 100) :
    (removedAt N k σ).card ≤ 2*(k+1)*witnessCount N k σ := by
  classical
  have he : (occurringWitnesses N k σ).card = witnessCount N k σ := by
    simp only [occurringWitnesses, witnessCount, Fintype.card_subtype]
  have hu := scaled_union_card (occurringWitnesses N k σ)
    (fun w => witnessVertices w.val) 1 (2*(k+1)) (fun w _ => by simpa using witness_vertices_bound w.val)
  simpa only [removedAt, Nat.one_mul, he, Nat.mul_comm] using hu

theorem removed_vertices_bound (N h : ℕ) (σ : PermutationTuples N 100) :
    (removedVertices N h σ).card ≤ witnessWeight N h σ := by
  classical
  exact Finset.card_biUnion_le.trans
    (nat_sum_mono (Finset.range h) _ _ (fun k _ => removedAt_bound N k σ))

theorem witness_vertex_removed {N h k : ℕ} (σ : PermutationTuples N 100)
    (w : ValidWitness N k) (hk : k < h) (hw : DescriptionOccurs w.val σ)
    (v : BipartiteVertex N) (hv : v ∈ witnessVertices w.val) :
    v ∈ removedVertices N h σ := by
  classical
  exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk,
    Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩,hv⟩⟩
end URMatching
