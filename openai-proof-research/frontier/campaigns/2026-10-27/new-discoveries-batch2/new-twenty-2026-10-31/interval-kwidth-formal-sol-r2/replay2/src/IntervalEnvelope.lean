import IntervalSuffix

namespace IntervalWidth
variable {α : Type*} [LinearOrder α] {n : Nat}

def leftEnvelope (z : α) (I : Fin n → Interval α) (S : Finset (Fin n))
    (block : Fin n → Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (I j).left ≤ suffixHeight z I S block (block j))

def rightEnvelope (z : α) (I : Fin n → Interval α) (S : Finset (Fin n))
    (block : Fin n → Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (I i).right ≤ suffixHeight z I S block (block i + 1))

theorem subset_leftEnvelope (z : α) (I : Fin n → Interval α) (S : Finset (Fin n))
    (block : Fin n → Nat) : S ⊆ leftEnvelope z I S block := by
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, selected_le_suffix z I S block j hj⟩

theorem rightEnvelope_subset_neighbors (z : α) (I : Fin n → Interval α)
    (S : Finset (Fin n)) (block : Fin n → Nat)
    (chronological : ∀ i j, block i < block j → i < j)
    (positive : ∀ i, z < (I i).right) : rightEnvelope z I S block ⊆ neighbors I S := by
  intro i hi
  exact later_suffix_neighbor z I S block chronological i (positive i)
    (Finset.mem_filter.mp hi).2

/-- A uniform bound on these actual suffix envelopes controls every Hall cut. -/
theorem width_le_of_envelopes (k d : Nat) (z : α) (I : Fin n → Interval α)
    (block : Fin n → Nat) (chronological : ∀ i j, block i < block j → i < j)
    (positive : ∀ i, z < (I i).right)
    (h : ∀ S : Finset (Fin n), (leftEnvelope z I S block).card ≤
      k * (rightEnvelope z I S block).card + d) : width k I ≤ d := by
  apply (width_le_iff_label_hall k d I).mpr
  intro S
  exact (Finset.card_le_card (subset_leftEnvelope z I S block)).trans
    ((h S).trans (Nat.add_le_add_right (Nat.mul_le_mul_left k
      (Finset.card_le_card (rightEnvelope_subset_neighbors z I S block chronological positive))) d))

end IntervalWidth
