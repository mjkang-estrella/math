/-
  UNCOMPILED DRAFT (Claude lane r130: Lean/lake were not run in this lane per memory restriction).
  MathDB 342364 — Ulas–Żmija Conjecture 6.1 (arXiv:1904.03398, Ramanujan J. 55 (2021)).

  This file fixes the literal statement layer only. The proof plan is in PLAN.md. No `sorry` is
  intended to survive; the `sorry`s below mark exactly the lemmas still to be formalised and must
  be removed before any endpoint claim.
-/
import Mathlib

open PowerSeries

namespace MathDB342364

/-- `geomStep k` is the power series `1/(1 - X^k)` over `ℤ`, written by coefficients. -/
noncomputable def geomStep (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if k ∣ n then 1 else 0

/-- Truncation level: for coefficient `n` only the factors `1/(1-X^{2^i})` with `2^i ≤ n` matter;
we use `i < n + 1`, which is always enough. `G_N(x) = 1/(1-x) * ∏_{i<N} 1/(1-x^{2^i})`. -/
noncomputable def G (N : ℕ) : PowerSeries ℤ :=
  geomStep 1 * ∏ i ∈ Finset.range N, geomStep (2 ^ i)

/-- `c m n` = coefficient of `x^n` in `C(x)^m`, `C = G_2` of the source (`c_1(n) = b(2n)`). -/
noncomputable def c (m n : ℕ) : ℤ :=
  PowerSeries.coeff ℤ n ((G (n + 1)) ^ m)

/-- Statement-correspondence sanity facts (to be proved by `decide`/`norm_num` after unfolding,
or replaced by a computable twin `cRec` defined via the recurrence
`(1-x)^m C_m(x) = (1+x)^m C_m(x^2)` together with a proof `c = cRec`). -/
theorem c_one_eq_two_mul (m : ℕ) : c m 1 = 2 * m := by
  sorry

/-- The refutation of the last clause of Conjecture 6.1 for `k = 3` (m = 15):
for every `n ≥ 1`, `2^(ν₂ n + 7) ∣ c 15 (4n) - c 15 n`. -/
theorem fifteen_divisibility (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) ^ (padicValNat 2 n + 7) ∣ c 15 (4 * n) - c 15 n := by
  sorry

/-- Literal negation of "equality holds for infinitely many n" in the case 4k+3, k = 3.
(If the difference were 0, Mathlib's `padicValInt 2 0 = 0 ≠ ν₂ n + 6`; otherwise divisibility
by `2^(ν₂ n + 7)` forces `padicValInt ≥ ν₂ n + 7`.) -/
theorem conj61_equality_clause_false :
    ¬ Set.Infinite {n : ℕ | 1 ≤ n ∧
        padicValInt 2 (c 15 (4 * n) - c 15 n) = padicValNat 2 n + 6} := by
  sorry

/-- Positive part (even case), full scope: for all k ≥ 1, n ≥ 1,
`ν₂(c_{2k}(4n) - c_{2k}(n)) = ν₂(n) + 2 ν₂(k) + 3` (difference nonzero). -/
theorem even_case (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    c (2 * k) (4 * n) - c (2 * k) n ≠ 0 ∧
    padicValInt 2 (c (2 * k) (4 * n) - c (2 * k) n) =
      padicValNat 2 n + 2 * padicValNat 2 k + 3 := by
  sorry

end MathDB342364
