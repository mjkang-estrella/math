import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Zeck
abbrev Pos := ℕ →₀ ℕ
def F (i : ℕ) : ℕ := Nat.fib (i + 1)
example : F 0 = 1 := by decide
example : F 2 = 2 := by decide
example : F 5 = 8 := by decide
example : F 6 = 13 := by decide
example (a b : ℕ) (h : a ≤ b) : a - 2 ≤ b := by omega
example (a : Pos) (i : ℕ) : a i * F i ≤ a.sum (fun j c => c * F j) := by
  have h := Finsupp.single_le_sum (f := a) (g := fun j c => c * F j) (fun j m => Nat.zero_le _) i
  have e : (Finsupp.single i (a i)).sum (fun j c => c * F j) = a i * F i := by simp
  rw [e] at h; exact h
example (a : Pos) (i : ℕ) : a i ≤ a.sum (fun _ c => c) := by
  exact Finsupp.single_eval_le_sum (f := a) (g := fun m => m) (by simp) (fun m => Nat.zero_le m) i
end Zeck
