import GraphChecker
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option linter.unusedSimpArgs false
namespace Nut8
/-- Sum of distinct binary places selected by a Boolean word. -/
def encodeBits (k : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range k, if b i then 2^i else 0

lemma encodeBits_lt (k : ℕ) (b : ℕ → Bool) : encodeBits k b < 2^k := by
  induction k with
  | zero => simp [encodeBits]
  | succ k ih =>
    simp only [encodeBits, Finset.sum_range_succ] at *
    cases h : b k <;> simp only [h, Bool.false_eq_true, ite_false, ite_true]
    · simpa using ih.trans_le (Nat.pow_le_pow_right (by omega) (by omega : k ≤ k+1))
    · rw [pow_succ]
      omega

lemma encodeBits_testBit (k : ℕ) (b : ℕ → Bool) (i : ℕ) :
    (encodeBits k b).testBit i = (decide (i < k) && b i) := by
  induction k with
  | zero => simp [encodeBits]
  | succ k ih =>
    have he : encodeBits (k+1) b = encodeBits k b + if b k then 2^k else 0 := by
      simp [encodeBits, Finset.sum_range_succ]
    rw [he]
    by_cases hik : i < k
    · have hi : i < k+1 := by omega
      cases h : b k <;> simp only [h, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
      · simpa [hi, hik] using ih
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hik, ih]
        simp [hi, hik]
    · by_cases hie : i = k
      · subst i
        have hz := Nat.testBit_lt_two_pow (encodeBits_lt k b)
        cases h : b k
        · simp [hz]
        · simp only [ite_true]
          rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, hz]
          simp
      · have hi : ¬ i < k+1 := by omega
        have hh : encodeBits k b + (if b k then 2^k else 0) < 2^i := by
          rw [← he]
          exact (encodeBits_lt _ _).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
        simp [Nat.testBit_lt_two_pow hh, hi]
end Nut8
