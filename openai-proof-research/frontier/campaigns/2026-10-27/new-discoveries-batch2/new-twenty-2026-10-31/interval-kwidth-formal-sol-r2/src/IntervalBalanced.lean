import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace IntervalWidth
open Finset
/-- Boundary of the q-th balanced consecutive block. -/
def blockStart (n m q : Nat) : Nat := q * (n / m) + min q (n % m)

theorem blockStart_zero (n m : Nat) : blockStart n m 0 = 0 := by
  simp [blockStart]

theorem blockStart_end (n m : Nat) (hm : 0 < m) : blockStart n m m = n := by
  have hr := Nat.mod_lt n hm
  simp only [blockStart, Nat.min_eq_right (Nat.le_of_lt hr)]
  exact Nat.div_add_mod n m

theorem blockStart_step (n m q : Nat) :
    blockStart n m (q+1) = blockStart n m q +
      (n / m + if q < n % m then 1 else 0) := by
  simp only [blockStart, Nat.add_mul, Nat.one_mul]
  split <;> rename_i h <;> omega

theorem blockStart_mono (n m : Nat) : Monotone (blockStart n m) := by
  apply monotone_nat_of_le_succ
  intro q
  rw [blockStart_step]
  exact Nat.le_add_right _ _

def balancedBlock (n m q : Nat) : Finset Nat :=
  Ico (blockStart n m q) (blockStart n m (q+1))

theorem balancedBlock_card (n m q : Nat) :
    (balancedBlock n m q).card = n / m + if q < n % m then 1 else 0 := by
  simp [balancedBlock, blockStart_step]

theorem balancedBlock_size (n m q : Nat) :
    (balancedBlock n m q).card = n / m ∨
    (balancedBlock n m q).card = n / m + 1 := by
  rw [balancedBlock_card]
  split_ifs <;> omega

theorem balancedBlock_disjoint (n m : Nat) {p q : Nat} (hpq : p < q) :
    Disjoint (balancedBlock n m p) (balancedBlock n m q) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' := Finset.mem_Ico.mp hi
  have hj' := Finset.mem_Ico.mp hj
  have h : blockStart n m (p+1) ≤ blockStart n m q := blockStart_mono n m (Nat.succ_le_of_lt hpq)
  omega

theorem balancedBlock_cover (n m : Nat) (hm : 0 < m) {i : Nat} (hi : i < n) :
    ∃ q < m, i ∈ balancedBlock n m q := by
  have H : ∀ t, i < blockStart n m t → ∃ q < t, i ∈ balancedBlock n m q := by
    intro t
    induction t with
    | zero => simp [blockStart]
    | succ t ih =>
      intro ht
      by_cases h : i < blockStart n m t
      · obtain ⟨q,hq,hqi⟩ := ih h
        exact ⟨q, by omega, hqi⟩
      · exact ⟨t, by omega, Finset.mem_Ico.mpr ⟨by omega,ht⟩⟩
  apply H m
  simpa [blockStart_end n m hm] using hi

#print axioms blockStart_zero
#print axioms blockStart_end
#print axioms blockStart_step
#print axioms blockStart_mono
#print axioms balancedBlock_card
#print axioms balancedBlock_size
#print axioms balancedBlock_disjoint
#print axioms balancedBlock_cover
end IntervalWidth
