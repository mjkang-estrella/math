module
public import GridNeighbours
@[expose] public section
namespace Grid343536

/-- Forgetting distinctions between cells maps the neighbour multiset accordingly. -/
theorem neighborCells_coarsen {V : Type*} [Fintype V] (G : SimpleGraph V)
    {r s : Setoid V} (h : r ≤ s) (u : V) :
    (neighborCells G r u).map (Quotient.map id h) = neighborCells G s u := by
  classical
  simp only [neighborCells, Multiset.map_map]
  rfl

/-- Equitable partitions are closed under arbitrary joins in the partition lattice. -/
theorem equitable_sSup {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Set (Setoid V)) (hS : ∀ r ∈ S, IsEquitable G r) :
    IsEquitable G (sSup S) := by
  apply (equitable_iff_neighborCells G (sSup S)).mpr
  have hle : sSup S ≤ Setoid.ker (neighborCells G (sSup S)) := by
    apply sSup_le
    intro r hr u v huv
    have hc := (equitable_iff_neighborCells G r).mp (hS r hr) u v huv
    have hm := congrArg (Multiset.map (Quotient.map id (le_sSup hr))) hc
    change neighborCells G (sSup S) u = neighborCells G (sSup S) v
    simpa only [neighborCells_coarsen] using hm
  exact fun u v huv => hle huv

noncomputable instance equitableSupSet {V : Type*} [Fintype V] (G : SimpleGraph V) :
    SupSet (EqPart G) where
  sSup S := ⟨sSup (Subtype.val '' S), equitable_sSup G _ (by
    rintro r ⟨p, hp, rfl⟩; exact p.property)⟩

/-- The complete lattice uses refinement order, with ordinary partition joins.
Meets are the joins of the equitable common refinements. -/
noncomputable instance equitableCompleteLattice {V : Type*} [Fintype V]
    (G : SimpleGraph V) : CompleteLattice (EqPart G) :=
  completeLatticeOfSup _ (by
    intro S
    constructor
    · intro p hp
      exact le_sSup (show p.val ∈ Subtype.val '' S from ⟨p, hp, rfl⟩)
    · intro p hp
      change sSup (Subtype.val '' S) ≤ p.val
      apply sSup_le
      rintro r ⟨q, hq, rfl⟩
      exact hp hq)

end Grid343536
