module
public import URMatchingFinite
@[expose] public section
namespace URMatching
universe u
variable {V : Type u}

/-- Delete vertices by keeping exactly those original edges with no deleted endpoint. -/
noncomputable def survivingEdges (M : Finset (Sym2 V)) (D : Finset V) : Finset (Sym2 V) := by
  classical
  exact M.filter fun e => ∀ v ∈ e, v ∉ D

/-- Edges lost to vertex deletion. -/
noncomputable def lostEdges (M : Finset (Sym2 V)) (D : Finset V) : Finset (Sym2 V) := by
  classical
  exact M.filter fun e => ∃ v ∈ e, v ∈ D

theorem surviving_isMatching {G : SimpleGraph V} {M : Finset (Sym2 V)}
    (hM : IsMatching G M) (D : Finset V) : IsMatching G (survivingEdges M D) := by
  classical
  constructor
  · intro e he; exact hM.1 e (Finset.mem_filter.mp he).1
  · intro e he f hf v hve hvf
    exact hM.2 e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 v hve hvf

/-- Disjoint matching edges admit distinct charges to deleted vertices. -/
theorem lost_card_le {G : SimpleGraph V} {M : Finset (Sym2 V)}
    (hM : IsMatching G M) (D : Finset V) : (lostEdges M D).card ≤ D.card := by
  classical
  let L := lostEdges M D
  have witness (e : L) : ∃ v : V, v ∈ e.val ∧ v ∈ D := by
    exact (Finset.mem_filter.mp e.property).2
  let charge : L → D := fun e => ⟨(witness e).choose, (witness e).choose_spec.2⟩
  apply Finset.card_le_card_of_injective (f := charge)
  intro e f hef
  apply Subtype.ext
  have hv : (charge e).val = (charge f).val := congrArg Subtype.val hef
  exact hM.2 e.val (Finset.mem_filter.mp e.property).1
    f.val (Finset.mem_filter.mp f.property).1
    (charge e).val (witness e).choose_spec.1 (hv ▸ (witness f).choose_spec.1)

theorem survive_add_lost (M : Finset (Sym2 V)) (D : Finset V) :
    (survivingEdges M D).card + (lostEdges M D).card = M.card := by
  classical
  have h : survivingEdges M D = M \ lostEdges M D := by
    ext e
    simp +contextual [survivingEdges, lostEdges]
  rw [h]
  exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)

/-- The retained matching loses at most one edge per deleted vertex; no perfect
matching of the surviving graph or equality of its side sizes is asserted. -/
theorem matching_retention {G : SimpleGraph V} {M : Finset (Sym2 V)}
    (hM : IsMatching G M) (D : Finset V) :
    M.card ≤ (survivingEdges M D).card + D.card := by
  rw [← survive_add_lost M D]
  exact Nat.add_le_add_left (lost_card_le hM D) _
end URMatching
