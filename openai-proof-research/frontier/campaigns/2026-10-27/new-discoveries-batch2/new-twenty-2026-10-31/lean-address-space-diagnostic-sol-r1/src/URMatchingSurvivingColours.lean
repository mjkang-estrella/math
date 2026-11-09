module
public import URMatchingRemovedVertices
@[expose] public section
namespace URMatching
open scoped Classical
def parallelDescription {N : ℕ} (x y : Fin N) (c d : Fin 100) : CycleDescription N 0 :=
  (⟨fun _ => x, fun i j _ => (Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm⟩,
   ⟨fun _ => y, fun i j _ => (Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm⟩,
   (fun _ => c), (fun _ => d))

theorem surviving_colour_unique {N h : ℕ} (σ : PermutationTuples N 100) (hh : 0 < h)
    (x y : Fin N) (hx : Sum.inl x ∉ removedVertices N h σ)
    (c d : Fin 100) (hc : σ c x = y) (hd : σ d x = y) : c = d := by
  classical
  by_contra hcd
  let w := parallelDescription x y c d
  have hw : ValidDescription w := fun _ => hcd
  have ho : DescriptionOccurs w σ := fun _ => ⟨hc,hd⟩
  apply hx
  apply witness_vertex_removed σ ⟨w,hw⟩ hh ho
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)

/-- Joint tuples have fewer than N/100 actually deleted vertices. -/
theorem exists_sparse_deletion_tuple (h : ℕ) : ∃ a : ℕ, 0 < a ∧ h ≤ a ∧
    ∃ σ : PermutationTuples (4*a) 100,
      100*(removedVertices (4*a) h σ).card < 4*a ∧
      (∀ A B : Finset (Fin (4*a)), A.card = a → B.card = a →
        ∃ c, ∃ x ∈ A, σ c x ∈ B) := by
  obtain ⟨a,ha,hh,σ,hweight,hholes⟩ := exists_joint_tuple h
  exact ⟨a,ha,hh,σ,(Nat.mul_le_mul_left 100 (removed_vertices_bound (4*a) h σ)).trans_lt hweight,hholes⟩
end URMatching
