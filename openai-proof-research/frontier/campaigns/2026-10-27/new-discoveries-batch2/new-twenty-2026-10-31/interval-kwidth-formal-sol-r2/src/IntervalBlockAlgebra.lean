import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
namespace IntervalWidth
open Finset
variable {K : Type*} [CommRing K]
/-- No monotonicity assumption on either threshold function. Zero-based blocks. -/
theorem block_telescoping (m : Nat) (k : K) (L R : Nat → K) :
    (∑ q ∈ range m, (L q - k * R (q+1))) =
    (∑ q ∈ range m, (L q - k * R q)) + k * (R 0 - R m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [sum_range_succ]
    rw [ih]
    ring

theorem completing_square_identity (k x : K) :
    (k+1) * (2*x-(k+1)*x^2) = 1 - ((k+1)*x-1)^2 := by ring

variable [LinearOrder K] [IsStrictOrderedRing K]
theorem completing_square_bound (k x : K) :
    (k+1) * (2*x-(k+1)*x^2) ≤ 1 := by
  rw [completing_square_identity]
  exact sub_le_self _ (sq_nonneg _)

/-- Quantitative all-block estimate with arbitrary supplied functions and errors. -/
theorem block_error_bound (m : Nat) (k a c B : K) (L R e : Nat → K)
    (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hpoint : ∀ q < m, L q - k * R q ≤ c)
    (hboundary : R 0 - R m ≤ B) (C : Nat → K)
    (hC : ∀ q < m, C q ≤ a * (L q - k * R (q+1)) + e q) :
    (∑ q ∈ range m, C q) ≤ a * ((m : K)*c + k*B) + ∑ q ∈ range m, e q := by
  calc
    _ ≤ ∑ q ∈ range m, (a * (L q - k * R (q+1)) + e q) :=
      sum_le_sum (fun q hq => hC q (mem_range.mp hq))
    _ = a * ((∑ q ∈ range m, (L q-k*R q)) + k*(R 0-R m)) +
        ∑ q ∈ range m, e q := by rw [sum_add_distrib, ← mul_sum, block_telescoping]
    _ ≤ a * ((m : K)*c + k*B) + ∑ q ∈ range m, e q := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ ha
      apply add_le_add
      · calc
          _ ≤ ∑ _q ∈ range m, c := sum_le_sum (fun q hq => hpoint q (mem_range.mp hq))
          _ = (m : K)*c := by simp
      · exact mul_le_mul_of_nonneg_left hboundary hk

#print axioms block_telescoping
#print axioms completing_square_identity
#print axioms completing_square_bound
#print axioms block_error_bound
end IntervalWidth
