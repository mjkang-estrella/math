import CrownVSwapWeight
import CrownVGreedyUnique

open Relation

/-!
# CrownV greedy normalization by finite legal swaps

One-step legal-swap relation and finite reachability of the greedy allocation.

`LegalSwap m d a b` holds iff `b` is obtained from `a` by one genuine swap
`swapAlloc a i j` with `i < j < m`, `a i < d i` and `0 < a j`; the definition
carries no preservation, descent, terminality or canonical-equality clause.

Main endpoint: for every `m r` and every `a` with prefix capacity and prefix
total `r` (no positivity premise on `m` or `r`), there exists `b` reachable
from `a` by a finite `ReflTransGen` chain of legal swaps such that `b` keeps
prefix capacity, keeps total `r`, is terminal (underfull earlier implies later
zero), and agrees with `greedyStep d r` on the whole prefix.

Mechanism (ordinary normal form): legal swaps strictly decrease the natural
weight `∑_{k<m} k * a k` (paid `swapAlloc_weight_strict`), preserve capacity
and total (paid `swapAlloc_capacity`, `swapAlloc_total`); a terminal
allocation is unique by the paid `greedy_terminal_unique`. Termination is by
plain induction on a weight bound, so `m = 0`, zero budgets and saturated
prefixes are covered by the same universal argument.
-/

namespace CrownV

/-- One legal swap on the prefix `k < m` against capacities `d`: move one unit
from a later nonempty column `j` to an earlier strictly-underfull column `i`,
via the literal `swapAlloc` update.  Only legality and the update; no
preservation, descent or canonicality clause. -/
def LegalSwap (m : Nat) (d : Nat → Nat) (a b : Nat → Nat) : Prop :=
  ∃ i j, i < j ∧ j < m ∧ a i < d i ∧ 0 < a j ∧ b = swapAlloc a i j

/-- Terminality of an allocation on the prefix: whenever an earlier column is
strictly underfull, every later column is empty. -/
def Terminal (m : Nat) (d : Nat → Nat) (a : Nat → Nat) : Prop :=
  ∀ i j, i < j → j < m → a i < d i → a j = 0

/-- Normalization core: by induction on a bound `n` for the weight
`∑_{k<m} k * a k`, every capacity-respecting allocation of total `r` reaches,
by finitely many legal swaps, a capacity-respecting terminal allocation of the
same total.  The bound induction gives plain structural recursion; the strict
weight decrease of each swap keeps the successor application below `n`. -/
theorem normalizeAux (m r : Nat) (d : Nat → Nat) :
    ∀ (n : Nat) (a : Nat → Nat),
      (∑ k ∈ Finset.range m, k * a k ≤ n) →
      (∀ k, k < m → a k ≤ d k) →
      (∑ k ∈ Finset.range m, a k = r) →
      ∃ b, ReflTransGen (LegalSwap m d) a b ∧
        (∀ k, k < m → b k ≤ d k) ∧
        (∑ k ∈ Finset.range m, b k = r) ∧
        Terminal m d b := by
  intro n
  induction n with
  | zero =>
    intro a hw hcap hsum
    refine ⟨a, ReflTransGen.refl, hcap, hsum, ?_⟩
    -- weight `≤ 0` forces every positive-weight column empty, hence terminality
    have hzero : ∑ k ∈ Finset.range m, k * a k = 0 := le_antisymm hw (Nat.zero_le _)
    intro i j hij hjm _
    have hmem : j ∈ Finset.range m := Finset.mem_range.mpr hjm
    have hjle : j * a j ≤ ∑ k ∈ Finset.range m, k * a k :=
      Finset.single_le_sum (f := fun k => k * a k) (fun k _ => Nat.zero_le _) hmem
    have hj0 : j * a j = 0 := le_antisymm (le_trans hjle (le_of_eq hzero)) (Nat.zero_le _)
    have hjnz : j ≠ 0 := by omega
    rcases Nat.mul_eq_zero.mp hj0 with hjz | hajz
    · exact absurd hjz (by omega)
    · exact hajz
  | succ n ih =>
    intro a hw hcap hsum
    by_cases hall : ∀ i j, i < j → j < m → a i < d i → a j = 0
    · exact ⟨a, ReflTransGen.refl, hcap, hsum, hall⟩
    · -- not terminal: a legal swap exists; perform it and descend in weight
      have key : ∃ i j, i < j ∧ j < m ∧ a i < d i ∧ 0 < a j := by
        by_contra hc
        exact hall (fun p q hpq hqm hpd =>
          match Nat.eq_zero_or_pos (a q) with
          | Or.inl h0 => h0
          | Or.inr hp => absurd (⟨p, q, hpq, hqm, hpd, hp⟩ : ∃ i j, i < j ∧ j < m ∧ a i < d i ∧ 0 < a j) hc)
      obtain ⟨i, j, hij, hjm, hid, haj⟩ := key
      have cap' : ∀ k, k < m → swapAlloc a i j k ≤ d k :=
        swapAlloc_capacity m i j d a hij hjm hid hcap
      have tot' : ∑ k ∈ Finset.range m, swapAlloc a i j k = r := by
        rw [swapAlloc_total m i j a hij hjm haj]
        exact hsum
      have w' : ∑ k ∈ Finset.range m, k * swapAlloc a i j k ≤ n := by
        have hlt : ∑ k ∈ Finset.range m, k * swapAlloc a i j k
            < ∑ k ∈ Finset.range m, k * a k :=
          swapAlloc_weight_strict m i j a hij hjm haj
        omega
      obtain ⟨b, chain, cb, tb, ub⟩ := ih _ w' cap' tot'
      exact ⟨b,
        ReflTransGen.trans
          (ReflTransGen.single (⟨i, j, hij, hjm, hid, haj, rfl⟩ :
            LegalSwap m d a (swapAlloc a i j)))
          chain,
        cb, tb, ub⟩

/-- Full normalization endpoint: from any prefix-feasible allocation of total
`r` there is, by finitely many legal swaps, a reachable allocation which keeps
prefix capacity, keeps total `r`, is terminal, and agrees with `greedyStep d r`
on every column `< m`.  No `m > 0` or positivity premise; outside-prefix values
are untouched by the swaps and unconstrained here. -/
theorem greedyNormalize (m r : Nat) (d a : Nat → Nat)
    (hcap : ∀ k, k < m → a k ≤ d k)
    (hsum : ∑ k ∈ Finset.range m, a k = r) :
    ∃ b, ReflTransGen (LegalSwap m d) a b ∧
      (∀ k, k < m → b k ≤ d k) ∧
      (∑ k ∈ Finset.range m, b k = r) ∧
      (∀ i j, i < j → j < m → b i < d i → b j = 0) ∧
      (∀ k, k < m → b k = greedyStep d r k) := by
    obtain ⟨b, chain, cb, tb, ub⟩ :=
      normalizeAux m r d (∑ k ∈ Finset.range m, k * a k) a (Nat.le_refl _) hcap hsum
    exact ⟨b, chain, cb, tb, ub, greedy_terminal_unique m r d b cb tb ub⟩

end CrownV
