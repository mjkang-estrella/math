import IntervalHall

namespace IntervalWidth
variable {α : Type*} [LE α] {n : Nat}

noncomputable def neighbors (I : Fin n → Interval α) (S : Finset (Fin n)) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j ∈ S, Compatible I i j)

theorem copy_neighbors_eq (k : Nat) (I : Fin n → Interval α) (S : Finset (Fin n)) :
    S.biUnion (copyNeighbors k I) = (neighbors I S).product Finset.univ := by
  classical
  ext c
  simp [copyNeighbors, neighbors]

theorem copy_neighbors_card (k : Nat) (I : Fin n → Interval α) (S : Finset (Fin n)) :
    (S.biUnion (copyNeighbors k I)).card = k * (neighbors I S).card := by
  classical
  rw [copy_neighbors_eq, Finset.product_eq_sprod]
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.mul_comm] using
    Finset.card_product (neighbors I S) (Finset.univ : Finset (Fin k))

theorem width_le_iff_label_hall (k d : Nat) (I : Fin n → Interval α) :
    width k I ≤ d ↔
      ∀ S : Finset (Fin n), S.card ≤ k * (neighbors I S).card + d := by
  simp_rw [width_le_iff_hall, copy_neighbors_card]

/-- The literal k-fold Hall deficiency identity, with maximum over all finite cuts. -/
noncomputable def maxDeficiency (k : Nat) (I : Fin n → Interval α) : Nat := by
  classical
  exact Finset.univ.sup (fun S : Finset (Fin n) => S.card - k * (neighbors I S).card)

theorem width_eq_maxDeficiency (k : Nat) (I : Fin n → Interval α) :
    width k I = maxDeficiency k I := by
  classical
  apply Nat.le_antisymm
  · apply (width_le_iff_label_hall k _ I).mpr
    intro S
    have h : S.card - k * (neighbors I S).card ≤ maxDeficiency k I :=
      Finset.le_sup (f := fun S => S.card - k * (neighbors I S).card) (Finset.mem_univ S)
    omega
  · apply Finset.sup_le
    intro S _
    have h := (width_le_iff_label_hall k (width k I) I).mp (Nat.le_refl _) S
    omega

end IntervalWidth
