import Mathlib
set_option maxRecDepth 2000
set_option maxHeartbeats 1600000

open Finset
namespace OddSubtraction

def eligible (S : Finset ℕ) (n : ℕ) : Finset ℕ := S.filter (fun k => k ≤ n)

/-- The complete recurrence and probability bounds for the source's randomized game. -/
structure Model (S : Finset ℕ) (a : ℕ → ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ a n
  le_one : ∀ n, a n ≤ 1
  empty : ∀ n, eligible S n = ∅ → a n = 0
  balance : ∀ n, ((eligible S n).card : ℝ) * a n =
    ((eligible S n).card : ℝ) - ∑ k∈eligible S n, a (n-k)

def centered (a : ℕ → ℝ) (n : ℕ) : ℝ := (-1:ℝ)^n * (1-2*a n)
def prefixSum (c : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j∈Finset.range n, c j

end OddSubtraction
