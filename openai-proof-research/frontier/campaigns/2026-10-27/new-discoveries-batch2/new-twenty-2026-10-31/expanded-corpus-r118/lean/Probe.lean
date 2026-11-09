import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Abel
example (a b : Multiset ℕ) (c : ℕ) : c • (a + b) = c • b + c • a := by rw [nsmul_add]; abel
#check @List.Perm.sum_eq
