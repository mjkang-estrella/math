module
public import URMatchingCycleExtraction
public import URMatchingDAG
public import URMatchingRectangleSides
@[expose] public section
namespace URMatching
universe u v
variable {I : Type u} {V : Type v} [Fintype I] [DecidableEq I] [DecidableEq V]

/-- Literal uniqueness on an indexed partial matching forces a genuine empty
rectangle. Neither acyclicity nor topological order is assumed. -/
theorem ur_indexed_empty_rectangle_sides (G : SimpleGraph V) (e : Sum I I ↪ V)
    (ur : IsUR G (indexedEdges e (Equiv.refl I))) :
    ∃ A B : Finset V, A.card = Fintype.card I / 2 ∧ B.card = Fintype.card I / 2 ∧
      (∀ x ∈ A, ∃ i, x = e (Sum.inl i)) ∧
      (∀ y ∈ B, ∃ i, y = e (Sum.inr i)) ∧
      Disjoint A B ∧ ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := by
  have diag : ∀ i, G.Adj (e (Sum.inl i)) (e (Sum.inr i)) := by
    intro i
    exact ur.1.1 _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have acyc : ∀ i, ¬ Relation.TransGen (CrossArc G e) i i := by
    intro i hi
    obtain ⟨l, hl⟩ := transGen_cycle_list (fun j hj => hj.1 rfl) hi
    exact ur_no_directed_cycle G e diag ur ⟨l, hl⟩
  obtain ⟨t, ht⟩ := finite_dag_topological (CrossArc G e) acyc
  let e' : Sum (Fin (Fintype.card I)) (Fin (Fintype.card I)) ↪ V :=
    (Equiv.sumCongr t.symm t.symm).toEmbedding.trans e
  obtain ⟨A, B, hA, hB, hleft, hright, hd, hempty⟩ :=
    ordered_empty_rectangle_sides (Fintype.card I) G e' (by
      intro i j hij hadj
      have hne : t.symm i ≠ t.symm j := fun h => hij (t.symm.injective h)
      have hh := ht _ _ ⟨hne, hadj⟩
      simpa using hh)
  refine ⟨A, B, hA, hB, ?_, ?_, hd, hempty⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := hleft x hx
    exact ⟨t.symm i, rfl⟩
  · intro y hy
    obtain ⟨i, rfl⟩ := hright y hy
    exact ⟨t.symm i, rfl⟩

end URMatching
