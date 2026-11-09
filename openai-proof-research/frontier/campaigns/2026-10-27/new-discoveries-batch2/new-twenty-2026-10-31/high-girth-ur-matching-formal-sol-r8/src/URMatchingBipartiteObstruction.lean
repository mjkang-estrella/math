module
public import URMatchingOrientationSides
public import URMatchingPartition
@[expose] public section
namespace URMatching
universe v
variable {V : Type v} [DecidableEq V]

/-- The directed-cycle/topological obstruction for ANY literal bipartite UR
matching, including partial matchings, odd size, and uncovered ambient vertices. -/
theorem ur_partition_empty_rectangle (G : SimpleGraph V) (P : V → Prop)
    (bip : AcrossPartition G P) (M : Finset (Sym2 V)) (ur : IsUR G M) :
    ∃ A B : Finset V, A.card = M.card / 2 ∧ B.card = M.card / 2 ∧
      (∀ x ∈ A, P x) ∧ (∀ y ∈ B, ¬ P y) ∧
      Disjoint A B ∧ ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := by
  classical
  apply ur_oriented_empty_rectangle_sides G M P ur
  intro a ha
  exact partition_orients_edge G P bip a (ur.1.1 a ha)
end URMatching
