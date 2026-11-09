import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# CrownV greedy prefix-sum identity

Literal finite-sum statement over an arbitrary capacity sequence `d : Nat → Nat`:
with `greedyPre d k = ∑_{i<k} d i` and greedy step
`greedyStep d r i = min (d i) (r - greedyPre d i)` (Nat truncated subtraction),
one has `∑_{i<k} greedyStep d r i = min r (greedyPre d k)` for all `d r k`.
No convergence, no bounds on `r`, all boundary cases included.
-/

namespace CrownV

/-- `greedyPre d k` is the literal finite prefix sum `∑_{i<k} d i`. -/
def greedyPre (d : Nat → Nat) (k : Nat) : Nat := ∑ i ∈ Finset.range k, d i

/-- Greedy amount taken at index `i`: capacity `d i` capped by remaining budget. -/
def greedyStep (d : Nat → Nat) (r : Nat) (i : Nat) : Nat :=
  min (d i) (r - greedyPre d i)

/-- Elementary truncation step: `min a b + min c (a - b) = min a (b + c)` on `Nat`. -/
theorem greedyStepAux (a b c : Nat) : min a b + min c (a - b) = min a (b + c) := by
  omega

/-- Main identity: greedy steps over a prefix sum to `min r (greedyPre d k)`, all `d r k`. -/
theorem greedyPrefix_sum (d : Nat → Nat) (r k : Nat) :
    ∑ i ∈ Finset.range k, greedyStep d r i = min r (greedyPre d k) := by
  induction k with
  | zero =>
    simp only [greedyPre, Finset.range_zero, Finset.sum_empty]
    omega
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h2 : greedyPre d (n + 1) = greedyPre d n + d n := by
      show ∑ i ∈ Finset.range (n + 1), d i = ∑ i ∈ Finset.range n, d i + d n
      rw [Finset.sum_range_succ]
    rw [h2]
    simp only [greedyStep]
    exact greedyStepAux r (greedyPre d n) (d n)

/-- Corollary: if the budget is at most the prefix total, greedy collects exactly `r`. -/
theorem greedyPrefix_sum_of_le (d : Nat → Nat) (r k : Nat) (h : r ≤ greedyPre d k) :
    ∑ i ∈ Finset.range k, greedyStep d r i = r := by
  rw [greedyPrefix_sum d r k]
  omega

end CrownV
