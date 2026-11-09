import IntervalEnvelope

namespace IntervalWidth
variable {α : Type*} [LE α] {n : Nat}

theorem width_positive (k : Nat) (I : Fin n → Interval α) (hn : 0 < n) :
    0 < width k I := by
  obtain ⟨P⟩ := width_attained k I
  exact (P.color ⟨0, hn⟩).isLt.trans_le' (Nat.zero_le _)

/-- Non-vacuity: if no edge is allowed, every class really is a singleton. -/
theorem width_of_no_edges (k : Nat) (I : Fin n → Interval α)
    (empty : ∀ i j, ¬ Compatible I i j) : width k I = n := by
  obtain ⟨P⟩ := width_attained k I
  have hp (j : Fin n) : P.parent j = none := by
    cases e : P.parent j with
    | none => rfl
    | some i => exact False.elim (empty i j (P.edge i j e))
  have hc : Function.Injective P.color := by
    intro i j h
    rw [(parent_none_iff_root P i).mp (hp i), (parent_none_iff_root P j).mp (hp j), h]
  apply Nat.le_antisymm (width_le_size k I)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.color hc

/-- All [0,1] intervals overlap: sampling-order edges cannot exist. -/
theorem overlapping_width (k n : Nat) :
    width k (fun _ : Fin n => (⟨0, 1⟩ : Interval Nat)) = n := by
  apply width_of_no_edges
  intro i j h
  exact Nat.not_succ_le_zero 0 h.2

theorem singleton_width (k : Nat) (I : Fin 1 → Interval α) : width k I = 1 := by
  have lo := width_positive k I (by decide)
  have hi := width_le_size k I
  omega

end IntervalWidth
