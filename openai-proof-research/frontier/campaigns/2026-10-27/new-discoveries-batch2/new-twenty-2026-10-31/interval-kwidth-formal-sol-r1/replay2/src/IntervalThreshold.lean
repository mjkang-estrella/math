import IntervalDeficiency

namespace IntervalWidth
variable {α : Type*} [Preorder α] {n k r : Nat} {I : Fin n → Interval α}

/-- Source ancestor compatibility follows from parent compatibility and valid intervals. -/
theorem Path.ancestor (P : HeapPartition k I r)
    (valid : ∀ j, (I j).left ≤ (I j).right) {a b : Fin n}
    (h : Path P.parent a b) : a = b ∨ Compatible I a b := by
  induction h with
  | refl => exact Or.inl rfl
  | @step i j _ e ih =>
    have he := P.edge i j e
    cases ih with
    | inl hi => exact Or.inr (hi ▸ he)
    | inr hi => exact Or.inr ⟨lt_trans hi.1 he.1,
        le_trans hi.2 (le_trans (valid i) he.2)⟩

/-- Every threshold cut gives a deterministic lower bound for literal tree width. -/
theorem threshold_lower [DecidableLE α] (k : Nat) (I : Fin n → Interval α) (x : α) :
    (Finset.univ.filter (fun j => (I j).left ≤ x)).card ≤
      k * (Finset.univ.filter (fun i => (I i).right ≤ x)).card + width k I := by
  classical
  let S := Finset.univ.filter (fun j => (I j).left ≤ x)
  let T := Finset.univ.filter (fun i => (I i).right ≤ x)
  have sub : neighbors I S ⊆ T := by
    intro i hi
    obtain ⟨j, hj, he⟩ := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      le_trans he.2 (Finset.mem_filter.mp hj).2⟩
  exact ((width_le_iff_label_hall k (width k I) I).mp (Nat.le_refl _) S).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left k (Finset.card_le_card sub)) _)

end IntervalWidth
