module
public import URMatchingWalkDescription
public import Mathlib.Combinatorics.SimpleGraph.Paths
@[expose] public section
namespace URMatching
open scoped Classical
/-- Every genuine short cycle based in the left side is among the deleted witnesses.
This theorem uses the actual mathlib Walk.IsCycle, not a replacement predicate. -/
theorem genuine_left_cycle_removed {N h : ℕ} (σ : PermutationTuples N 100)
    (u : Fin N) (p : (permutationGraph σ).Walk (.inl u) (.inl u))
    (hp : p.IsCycle) (hs : p.length ≤ 2*h) :
    Sum.inl u ∈ removedVertices N h σ := by
  have he := permutation_closed_walk_even σ p
  have hl := hp.three_le_length
  let k := p.length/2-1
  have hk : 0 < k := by dsimp [k]; omega
  have hlen : p.length = 2*(k+1) := by dsimp [k]; omega
  have hkh : k < h := by omega
  obtain ⟨w,hw,hbase⟩ := closed_walk_description σ u hk p hlen hp.support_nodup
  apply witness_vertex_removed σ w hkh hw
  simp only [witnessVertices, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl ⟨0, congrArg Sum.inl hbase⟩
end URMatching
