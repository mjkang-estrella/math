import IntervalBalanced
import IntervalEnvelope
namespace IntervalWidth
open Finset

theorem block_count_decomposition {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (block : ι → Nat) (m : Nat) (hb : ∀ i ∈ s, block i < m) :
    s.card = ∑ q ∈ range m, (s.filter (fun i => block i = q)).card := by
  exact Finset.card_eq_sum_card_fiberwise (fun i hi => Finset.mem_range.mpr (hb i hi))

noncomputable def balancedLabel (n m : Nat) (hm : 0 < m) (i : Fin n) : Nat :=
  Classical.choose (balancedBlock_cover n m hm i.isLt)

theorem balancedLabel_mem (n m : Nat) (hm : 0 < m) (i : Fin n) :
    balancedLabel n m hm i < m ∧ i.val ∈ balancedBlock n m (balancedLabel n m hm i) :=
  Classical.choose_spec (balancedBlock_cover n m hm i.isLt)

theorem balancedLabel_chronological (n m : Nat) (hm : 0 < m) (i j : Fin n)
    (h : balancedLabel n m hm i < balancedLabel n m hm j) : i < j := by
  have hi := (Finset.mem_Ico.mp (balancedLabel_mem n m hm i).2).2
  have hj := (Finset.mem_Ico.mp (balancedLabel_mem n m hm j).2).1
  have hb : blockStart n m (balancedLabel n m hm i + 1) ≤
      blockStart n m (balancedLabel n m hm j) := blockStart_mono n m h
  exact hi.trans_le (hb.trans hj)

variable {α : Type*} [LinearOrder α] {n : Nat}
/-- Counts in an arbitrary block at an arbitrary supplied threshold function. -/
noncomputable def blockLeftCount (I : Fin n → Interval α) (block : Fin n → Nat)
    (h : Nat → α) (q : Nat) : Nat :=
  (Finset.univ.filter (fun i => block i = q ∧ (I i).left ≤ h q)).card
noncomputable def blockRightCount (I : Fin n → Interval α) (block : Fin n → Nat)
    (h : Nat → α) (q : Nat) : Nat :=
  (Finset.univ.filter (fun i => block i = q ∧ (I i).right ≤ h (q+1))).card

theorem left_count_sum (z : α) (I : Fin n → Interval α) (S : Finset (Fin n))
    (block : Fin n → Nat) (m : Nat) (hb : ∀ i, block i < m) :
    (leftEnvelope z I S block).card =
      ∑ q ∈ range m, blockLeftCount I block (suffixHeight z I S block) q := by
  classical
  rw [block_count_decomposition (leftEnvelope z I S block) block m (fun i _ => hb i)]
  apply sum_congr rfl
  intro q _
  congr 1
  ext i
  simp only [leftEnvelope, mem_filter, mem_univ, true_and]
  constructor <;> rintro ⟨h,h'⟩
  · exact ⟨h', by simpa [h'] using h⟩
  · exact ⟨by simpa [h] using h',h⟩

theorem right_count_sum (z : α) (I : Fin n → Interval α) (S : Finset (Fin n))
    (block : Fin n → Nat) (m : Nat) (hb : ∀ i, block i < m) :
    (rightEnvelope z I S block).card =
      ∑ q ∈ range m, blockRightCount I block (suffixHeight z I S block) q := by
  classical
  rw [block_count_decomposition (rightEnvelope z I S block) block m (fun i _ => hb i)]
  apply sum_congr rfl
  intro q _
  congr 1
  ext i
  simp only [rightEnvelope, mem_filter, mem_univ, true_and]
  constructor <;> rintro ⟨h,h'⟩
  · exact ⟨h', by simpa [h'] using h⟩
  · exact ⟨by simpa [h] using h',h⟩

/-- All-cut bound (D), written additively over naturals to avoid truncated subtraction. -/
theorem all_cut_block_bound (k : Nat) (z : α) (I : Fin n → Interval α)
    (block : Fin n → Nat) (m : Nat) (hb : ∀ i, block i < m)
    (chronological : ∀ i j, block i < block j → i < j)
    (positive : ∀ i, z < (I i).right) (S : Finset (Fin n)) :
    S.card + k * (∑ q ∈ range m, blockRightCount I block (suffixHeight z I S block) q) ≤
    (∑ q ∈ range m, blockLeftCount I block (suffixHeight z I S block) q) +
      k * (neighbors I S).card := by
  rw [← left_count_sum z I S block m hb, ← right_count_sum z I S block m hb]
  exact Nat.add_le_add (Finset.card_le_card (subset_leftEnvelope z I S block))
    (Nat.mul_le_mul_left k (Finset.card_le_card
      (rightEnvelope_subset_neighbors z I S block chronological positive)))

#print axioms block_count_decomposition
#print axioms balancedLabel
#print axioms balancedLabel_mem
#print axioms balancedLabel_chronological
#print axioms blockLeftCount
#print axioms blockRightCount
#print axioms left_count_sum
#print axioms right_count_sum
#print axioms all_cut_block_bound
end IntervalWidth
