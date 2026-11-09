# Exact remaining Props

All six remain open. These are definitions, not added assumptions in the Lean environment. Each conditional endpoint explicitly takes their conjunction as an argument.

```lean
def EvenFormula : Prop := ∀ k n : ℕ, 1 ≤ k → 1 ≤ n →
  diff (2*k) n ≠ 0 ∧ val (2*k) n = targetEven k n

def OddOneBound : Prop := ∀ k n : ℕ, 1 ≤ n →
  diff (4*k+1) n ≠ 0 ∧ padicValNat 2 n + 3 ≤ val (4*k+1) n

def OddThreeBound : Prop := ∀ k n : ℕ, 1 ≤ n →
  diff (4*k+3) n ≠ 0 ∧ padicValNat 2 n + 6 ≤ val (4*k+3) n

def OddOneEquality : Prop := ∀ k n : ℕ, 1 ≤ n → n % 2 = 1 →
  val (4*k+1) n = padicValNat 2 n + 3

def OddThreeEquality : Prop := ∀ k n : ℕ, 1 ≤ n →
  (((4*k+3)%16 = 3 ∨ (4*k+3)%16 = 7) ∧ n%2 = 1 ∨
   (4*k+3)%16 = 11 ∧ n%4 = 2) →
  val (4*k+3) n = padicValNat 2 n + 6

def FifteenBound : Prop := ∀ t n : ℕ, 1 ≤ n →
  diff (16*t+15) n ≠ 0 ∧ padicValNat 2 n + 7 ≤ val (16*t+15) n
```
