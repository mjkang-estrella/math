# Statement correspondence for 371207 (draft, UNCOMPILED)

**Status.** No exact proof exists, so there is no proof certificate. This file fixes the endpoint that a future proof would have to hit, and gives definitions so root or a Sol worker can compile the statement. **Nothing below was compiled.** Claude lane rule: no Lean was run.

## Sources and literal statements

**MathDB 371207** (record in `expanded-corpus-r134/raw/371207.jsonl`):

> For any fixed k ≥ 5, there exists some N such that, for any n ≥ N, there are no k-player profiles in equilibrium on Q_n.

**Primary source:** Stylianou, arXiv:2510.25392v1, Conjecture 1.1, with the definitions in Section 1 (see PROOF.md Part A).

## Correspondence table

| Source notion | Draft Lean | Notes |
|---|---|---|
| Q_n = {0,1}^n | `Fin n → Bool` | |
| Hamming distance | `hd x y = (univ.filter (x · ≠ y ·)).card` | |
| profile (positions need not be distinct) | `Fin k → Cube n` | no distinctness hypothesis |
| A_i claims x | `∀ j, hd x (P i) ≤ hd x (P j)` | |
| score with equal tie-splitting | `2^{-n} Σ_x [claims] / #claimers` | co-located players each count |
| moving to any vertex, occupied allowed | `Function.update P i y`, with `y` arbitrary | |
| equilibrium (no strict improvement) | `∀ i y, score (update P i y) i ≤ score P i` | |
| Conjecture 1.1 | `DayJohnson` | |
| refutation target | `¬ DayJohnson` | equivalently, the ∃∀∃∃ form below |

## Draft Lean source (UNCOMPILED)

```lean
import Mathlib

open Finset BigOperators

namespace Voronoi371207

abbrev Cube (n : ℕ) := Fin n → Bool

def hd {n : ℕ} (x y : Cube n) : ℕ := (univ.filter fun i => x i ≠ y i).card

abbrev Profile (n k : ℕ) := Fin k → Cube n

/-- `i` claims voter `x` in profile `P`. -/
def Claims {n k : ℕ} (P : Profile n k) (x : Cube n) (i : Fin k) : Prop :=
  ∀ j, hd x (P i) ≤ hd x (P j)

instance {n k : ℕ} (P : Profile n k) (x : Cube n) (i : Fin k) : Decidable (Claims P x i) := by
  unfold Claims; infer_instance

/-- Stylianou's score σ_P(A_i) = 2^{-n} Σ_{x ∈ V_P(A_i)} 1 / t_P(x). -/
def score {n k : ℕ} (P : Profile n k) (i : Fin k) : ℚ :=
  (∑ x : Cube n, if Claims P x i then
      (1 : ℚ) / ((univ.filter fun j => Claims P x j).card : ℚ) else 0) / 2 ^ n

def IsEquilibrium {n k : ℕ} (P : Profile n k) : Prop :=
  ∀ (i : Fin k) (y : Cube n), score (Function.update P i y) i ≤ score P i

/-- Day–Johnson conjecture (Stylianou, Conjecture 1.1), literal form. -/
def DayJohnson : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : Profile n k, ¬ IsEquilibrium P

/-- Refutation target: the exact negation, in the ∃∀∃∃ form. -/
theorem not_dayJohnson_iff :
    ¬ DayJohnson ↔ ∃ k : ℕ, 5 ≤ k ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ P : Profile n k, IsEquilibrium P := by
  unfold DayJohnson
  push_neg
  rfl  -- may need `simp only [not_not]`; UNCOMPILED

/-- The 8-player subspace profile for multiplicities `m : Fin 7 → ℕ` (functional f = i+1 on F_2^3). -/
-- def subspaceProfile (m : Fin 7 → ℕ) : Profile (∑ i, m i) 8 := ...   -- to be written by the formal worker

end Voronoi371207
```

## Notes for a future formal endpoint

- An accepted endpoint would be `theorem refutes : ¬ DayJohnson`, proved by exhibiting, for every N, the profile `subspaceProfile (t+1, t, …, t)` with 7t + 1 ≥ N, together with a proof of `IsEquilibrium`.
- **Lemma 1** (PROOF.md B.1) reduces `IsEquilibrium` to player 0. It is formalizable cheaply: translation by p_b is an isometry and permutes the players.
- **Lemma 2** (B.2) reduces the condition to a finite family of binomial-sum inequalities indexed by shapes c. This is formalizable, but bookkeeping-heavy.
- The remaining inequality for all t is **Missing Lemma M** (PROOF.md Part D). It is analytic, there is currently no exact route, and its Lean cost is prohibitive.
- **Finite instances.** For example, `IsEquilibrium (subspaceProfile (2,1,1,1,1,1,1))` on Q_8 is a finite statement that could be checked by kernel `decide`; native_decide is forbidden. But finite instances cannot refute an "eventually" statement and earn no credit.
