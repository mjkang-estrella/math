import Defs
namespace Cover377831
open scoped BigOperators

def W (p : Point 3) : ℕ := if p ∉ H then 0 else if p = (0,0,2) then 2
  else if p = (0,2,2) then 0 else 1

theorem total_weight : ∑ p : Point 3, W p = 17 := by decide

theorem line_weight : ∀ l : Line 3, (∑ p : Point 3, if OnLine p l then W p else 0) ≤ 2 := by decide

theorem weighted_bound (L : Finset (Line 3)) (hL : Covers H L) : 17 ≤ 2 * L.card := by
  have hp (p : Point 3) : W p ≤ ∑ l ∈ L, if OnLine p l then W p else 0 := by
    by_cases h : p ∈ H
    · obtain ⟨l, hl, hpl⟩ := hL p h
      exact le_trans (by simp [hpl]) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hl)
    · simp [W, h]
  calc
    17 = ∑ p : Point 3, W p := total_weight.symm
    _ ≤ ∑ p : Point 3, ∑ l ∈ L, if OnLine p l then W p else 0 := Finset.sum_le_sum (fun p _ => hp p)
    _ = ∑ l ∈ L, ∑ p : Point 3, if OnLine p l then W p else 0 := Finset.sum_comm
    _ ≤ ∑ _l ∈ L, 2 := Finset.sum_le_sum (fun l _ => line_weight l)
    _ = 2 * L.card := by simp [Nat.mul_comm]

def vertical : Finset (Line 3) := Finset.univ.filter (fun l => l.1 = 2)
theorem vertical_card : vertical.card = 9 := by decide
theorem vertical_covers : Covers H vertical := by unfold Covers; decide

theorem covering_number : CoverNumber H = 9 := by
  have hne : {n | ∃ L : Finset (Line 3), L.card = n ∧ Covers H L}.Nonempty :=
    ⟨9, vertical, vertical_card, vertical_covers⟩
  apply le_antisymm
  · exact Nat.sInf_le ⟨vertical, vertical_card, vertical_covers⟩
  · apply le_csInf hne
    rintro n ⟨L, rfl, hL⟩
    have := weighted_bound L hL
    omega
end Cover377831
