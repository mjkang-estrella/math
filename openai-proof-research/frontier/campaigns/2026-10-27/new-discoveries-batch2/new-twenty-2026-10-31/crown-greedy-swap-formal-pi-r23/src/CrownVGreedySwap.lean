import Mathlib.Data.Finset.Range
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# CrownV greedy legal swap

The elementary legal-swap step of the reviewed greedy normal-form proof.  For
arbitrary capacities `d : Nat → Nat` and allocation `a : Nat → Nat` on the
finite column prefix `k < m`: whenever `i < j < m`, `a i < d i` and `a j > 0`,
one unit of allocation may move from the later column `j` to the earlier
column `i`.  The new allocation `b = swapAlloc a i j` is the composition of
two ordinary `Function.update`s: `b i = a i + 1`, `b j = a j - 1`, and every
other value unchanged.

Proved here, for all `m i j d a`:

* `swapAlloc_capacity` : `a k ≤ d k` on `k < m` implies `b k ≤ d k` on `k < m`
  (prefix capacity preservation);
* `swapAlloc_total` : `∑_{k<m} b k = ∑_{k<m} a k` (total load preserved);
* `swapAlloc_weight_strict` : `∑_{k<m} k * b k < ∑_{k<m} k * a k`
  (strict decrease of the weighted load).

Every boundary case (`m = 0`, zero capacities, saturated columns, `a j = 1`)
is covered by the single universal statements; the only hypotheses are the
swap hypotheses themselves.  This is exactly the descent step of the ordinary
greedy exchange argument: no search procedure, no characteristic or
coefficient-ring assumption, no answer-encoding relation.
-/

namespace CrownV

/-- The allocation obtained from `a` by one legal swap `j → i`: the plain
function `a` with two ordinary function updates, `+1` at `i` and `-1` at `j`,
all other values left untouched. -/
def swapAlloc (a : Nat → Nat) (i j : Nat) : Nat → Nat :=
  Function.update (Function.update a i (a i + 1)) j (a j - 1)

/-- Pointwise reading of the two updates, in application order. -/
theorem swapAlloc_eval (a : Nat → Nat) (i j k : Nat) :
    swapAlloc a i j k = if k = j then a j - 1 else if k = i then a i + 1 else a k := by
  unfold swapAlloc
  rw [Function.update_apply, Function.update_apply]

/-- Value at the receiving column `k = i`: one unit gained. -/
theorem swapAlloc_at_i (a : Nat → Nat) (i j k : Nat) (hij : i < j) (h : k = i) :
    swapAlloc a i j k = a k + 1 := by
  have hne : i ≠ j := ne_of_lt hij
  rw [swapAlloc_eval, if_neg (show k ≠ j from fun hh => hne (h.symm.trans hh)), if_pos h, ← h]

/-- Value at the losing column `k = j`: one unit lost. -/
theorem swapAlloc_at_j (a : Nat → Nat) (i j k : Nat) (h : k = j) :
    swapAlloc a i j k = a k - 1 := by
  rw [swapAlloc_eval, if_pos h, ← h]

/-- Value at any column distinct from both `i` and `j`: unchanged. -/
theorem swapAlloc_at_else (a : Nat → Nat) (i j k : Nat) (h1 : k ≠ i) (h2 : k ≠ j) :
    swapAlloc a i j k = a k := by
  rw [swapAlloc_eval, if_neg h2, if_neg h1]

/-- Prefix capacity preservation: if `a` respects the capacities `d` on the
prefix `k < m`, then so does the swapped allocation, in particular at the
receiving column `i` (where `a i < d i` opens room) and at the losing column
`j` (where removal only decreases).  No boundary exclusions. -/
theorem swapAlloc_capacity (m i j : Nat) (d a : Nat → Nat)
    (hij : i < j) (hjm : j < m) (hid : a i < d i)
    (hcap : ∀ k, k < m → a k ≤ d k) :
    ∀ k, k < m → swapAlloc a i j k ≤ d k := by
  intro k hk
  by_cases h1 : k = i
  · rw [swapAlloc_at_i a i j k hij h1]
    have hid' : a k < d k := by rw [h1]; exact hid
    omega
  · by_cases h2 : k = j
    · rw [swapAlloc_at_j a i j k h2]
      have hc : a k ≤ d k := by rw [h2]; exact hcap j hjm
      omega
    · rw [swapAlloc_at_else a i j k h1 h2]
      exact hcap k hk

/-- Pointwise bookkeeping identity: the swapped allocation plus the indicator
of `j` equals the original allocation plus the indicator of `i`.  On `Nat
this is the literal unit moved from `j` to `i`; the column `j` loses one unit
which is exactly compensated, using `a j > 0`. -/
theorem swapAlloc_shift (a : Nat → Nat) (i j k : Nat) (hij : i < j) (haj : 0 < a j) :
    swapAlloc a i j k + (if k = j then 1 else 0) = a k + (if k = i then 1 else 0) := by
  have hne : i ≠ j := ne_of_lt hij
  by_cases h1 : k = i
  · have hkj : k ≠ j := fun hh => hne (h1.symm.trans hh)
    rw [swapAlloc_at_i a i j k hij h1, if_neg hkj, if_pos h1]
    omega
  · rw [if_neg h1]
    by_cases h2 : k = j
    · rw [swapAlloc_at_j a i j k h2, if_pos h2]
      have haj' : 0 < a k := by rw [h2]; exact haj
      omega
    · rw [swapAlloc_at_else a i j k h1 h2, if_neg h2]

/-- Total load preserved: the prefix sum of the swapped allocation equals the
prefix sum of the original allocation, for every prefix length `m` containing
both touched columns. -/
theorem swapAlloc_total (m i j : Nat) (a : Nat → Nat)
    (hij : i < j) (hjm : j < m) (haj : 0 < a j) :
    ∑ k ∈ Finset.range m, swapAlloc a i j k = ∑ k ∈ Finset.range m, a k := by
  have him : i < m := lt_trans hij hjm
  have hdi : ∑ x ∈ Finset.range m, (if x = i then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr him)
      (fun b _ hb => if_neg hb)]
    exact if_pos rfl
  have hdj : ∑ x ∈ Finset.range m, (if x = j then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hjm)
      (fun b _ hb => if_neg hb)]
    exact if_pos rfl
  have step : (∑ k ∈ Finset.range m, swapAlloc a i j k)
      + (∑ k ∈ Finset.range m, (if k = j then 1 else 0))
      = (∑ k ∈ Finset.range m, a k)
        + (∑ k ∈ Finset.range m, (if k = i then 1 else 0)) := by
    calc (∑ k ∈ Finset.range m, swapAlloc a i j k)
        + (∑ k ∈ Finset.range m, (if k = j then 1 else 0))
        = ∑ x ∈ Finset.range m, (swapAlloc a i j x + (if x = j then 1 else 0)) :=
          Finset.sum_add_distrib.symm
      _ = ∑ x ∈ Finset.range m, (a x + (if x = i then 1 else 0)) :=
          Finset.sum_congr rfl fun x _ => swapAlloc_shift a i j x hij haj
      _ = (∑ k ∈ Finset.range m, a k)
          + (∑ k ∈ Finset.range m, (if k = i then 1 else 0)) := Finset.sum_add_distrib
  rw [hdj, hdi] at step
  omega

/-- Weighted load strictly decreases: with weight `k` on column `k`, moving
one unit from the later column `j` to the earlier column `i < j` strictly
decreases `∑_{k<m} k * a k`.  The finite weighted sum is a plain natural
number; no convergence or finiteness side conditions. -/
theorem swapAlloc_weight_strict (m i j : Nat) (a : Nat → Nat)
    (hij : i < j) (hjm : j < m) (haj : 0 < a j) :
    ∑ k ∈ Finset.range m, k * swapAlloc a i j k
      < ∑ k ∈ Finset.range m, k * a k := by
  have him : i < m := lt_trans hij hjm
  have hwi : ∑ x ∈ Finset.range m, x * (if x = i then 1 else 0) = i := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr him)
      (fun b _ hb => by rw [if_neg hb, mul_zero])]
    simp
  have hwj : ∑ x ∈ Finset.range m, x * (if x = j then 1 else 0) = j := by
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hjm)
      (fun b _ hb => by rw [if_neg hb, mul_zero])]
    simp
  have key : ∀ x ∈ Finset.range m,
      x * swapAlloc a i j x + x * (if x = j then 1 else 0)
        = x * a x + x * (if x = i then 1 else 0) := by
    intro x _
    have hs := swapAlloc_shift a i j x hij haj
    calc x * swapAlloc a i j x + x * (if x = j then 1 else 0)
        = x * (swapAlloc a i j x + (if x = j then 1 else 0)) := (mul_add x _ _).symm
      _ = x * (a x + (if x = i then 1 else 0)) := by rw [hs]
      _ = x * a x + x * (if x = i then 1 else 0) := mul_add x _ _
  have step : (∑ x ∈ Finset.range m, x * swapAlloc a i j x)
      + (∑ x ∈ Finset.range m, x * (if x = j then 1 else 0))
      = (∑ x ∈ Finset.range m, x * a x)
        + (∑ x ∈ Finset.range m, x * (if x = i then 1 else 0)) := by
    calc (∑ x ∈ Finset.range m, x * swapAlloc a i j x)
        + (∑ x ∈ Finset.range m, x * (if x = j then 1 else 0))
        = ∑ y ∈ Finset.range m
            (x * swapAlloc a i j y + x * (if x = j then 1 else 0)) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ x ∈ Finset.range m, x * swapAlloc a i j x
            + ∑ x ∈ Finset.range m, x * (if x = j then 1 else 0) := Finset.sum_add_distrib
      _ = (∑ x ∈ Finset.range m, x * a x)
          + (∑ x ∈ Finset.range m, x * (if x = i then 1 else 0)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl key
  rw [hwj, hwi] at step
  omega

end CrownV
