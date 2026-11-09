module
public import GridPropagation
@[expose] public section
namespace Grid343536
open Finset

/-- The actual multiset of neighbour cells, with repetitions retained. -/
noncomputable def neighborCells {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : Setoid V) (u : V) : Multiset (Quotient r) := by
  classical
  exact ((univ.filter (G.Adj u)).val).map (Quotient.mk r)

theorem neighborCells_count {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : Setoid V) [DecidableEq (Quotient r)] (u w : V) :
    Multiset.count (Quotient.mk r w) (neighborCells G r u) =
      Nat.card {x // G.Adj u x ∧ r x w} := by
  classical
  simp only [neighborCells, Multiset.count_map]
  simp only [← Finset.filter_val,
    filter_filter, Quotient.eq]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change (univ.filter (fun a => G.Adj u a ∧ r w a)).card =
    (univ.filter (fun a => G.Adj u a ∧ r a w)).card
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact and_congr_right (fun _ => ⟨r.symm, r.symm⟩)

theorem equitable_iff_neighborCells {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : Setoid V) :
    IsEquitable G r ↔ ∀ u v, r u v → neighborCells G r u = neighborCells G r v := by
  classical
  constructor
  · intro hr u v huv
    apply Multiset.ext.mpr
    intro q
    obtain ⟨w, rfl⟩ := Quotient.exists_rep q
    simpa only [neighborCells_count] using hr u v huv w
  · intro h u v huv w
    simpa only [neighborCells_count] using congrArg (Multiset.count (Quotient.mk r w)) (h u v huv)
end Grid343536
