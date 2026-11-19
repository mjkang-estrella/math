import K8Cnf
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# The seven forbidden signed four-point patterns

For `Q : ℕ → ℕ → ℝ` (point `x`, coordinate `c`) the entry `(i, c, s)` of a
pattern says that for the `i`-th pair `(a, b)` of `K₄`,
`sgn(s) * (Q b c - Q a c) > |Q b j - Q a j|` for both coordinates `j ≠ c`.
Each representative pattern in `K8.reps` is infeasible over the reals: a
nonnegative combination of its strict inequalities is `0 < 0`.  `linarith`
finds the combination.
-/

set_option linter.unusedSimpArgs false

namespace K8

/-- `+1` or `-1`. -/
def sgnR (b : Bool) : ℝ := if b then 1 else -1

/-- The real inequalities expressed by one pattern entry. -/
def DomS (Q : ℕ → ℕ → ℝ) (e : ℕ × ℕ × Bool) : Prop :=
  ∀ j, j < 3 → j ≠ e.2.1 →
    |Q (e4.getD e.1 (0, 0)).2 j - Q (e4.getD e.1 (0, 0)).1 j| <
      sgnR e.2.2 * (Q (e4.getD e.1 (0, 0)).2 e.2.1 - Q (e4.getD e.1 (0, 0)).1 e.2.1)

theorem forall_lt_three {P : ℕ → Prop} : (∀ j, j < 3 → P j) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h; exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega)⟩
  · rintro ⟨h0, h1, h2⟩ j hj
    interval_cases j <;> assumption

theorem rep_infeasible (r : ℕ) (hr : r < 7) (Q : ℕ → ℕ → ℝ)
    (h : ∀ e ∈ reps.getD r [], DomS Q e) : False := by
  interval_cases r <;>
  · simp only [reps, List.getD_cons_succ, List.getD_cons_zero, List.forall_mem_cons,
      List.forall_mem_nil, DomS, forall_lt_three, e4, sgnR] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero, ne_eq, OfNat.ofNat_ne_zero,
      OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat, one_ne_zero, zero_ne_one,
      not_false_eq_true, not_true_eq_false, false_implies, true_implies, Bool.false_eq_true,
      ite_true, ite_false, abs_lt, one_mul, neg_mul, and_true, true_and] at h
    linarith

end K8
