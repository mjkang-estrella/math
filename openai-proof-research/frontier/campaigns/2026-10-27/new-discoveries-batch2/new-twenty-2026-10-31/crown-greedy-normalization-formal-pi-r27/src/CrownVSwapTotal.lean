import CrownVSwapCapacity

/-! Pointwise unit-balance and finite-prefix sum preservation. Extracted from r23 draft with compiler-prescribed conditional names and one redundant tactic removed; weight descent remains unpaid. -/

namespace CrownV

/-- Pointwise bookkeeping identity: the swapped allocation plus the indicator
of `j` equals the original allocation plus the indicator of `i`.  On `Nat
this is the literal unit moved from `j` to `i`; the column `j` loses one unit
which is exactly compensated, using `a j > 0`. -/
theorem swapAlloc_shift (a : Nat → Nat) (i j k : Nat) (hij : i < j) (haj : 0 < a j) :
    swapAlloc a i j k + (if k = j then 1 else 0) = a k + (if k = i then 1 else 0) := by
  have hne : i ≠ j := ne_of_lt hij
  by_cases h1 : k = i
  · have hkj : k ≠ j := fun hh => hne (h1.symm.trans hh)
    rw [swapAlloc_at_i a i j k hij h1, ite_eq_right hkj, ite_eq_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : k = j
    · rw [swapAlloc_at_j a i j k h2, ite_eq_left h2]
      have haj' : 0 < a k := by rw [h2]; exact haj
      omega
    · rw [swapAlloc_at_else a i j k h1 h2, ite_eq_right h2]

/-- Total load preserved: the prefix sum of the swapped allocation equals the
prefix sum of the original allocation, for every prefix length `m` containing
both touched columns. -/
theorem swapAlloc_total (m i j : Nat) (a : Nat → Nat)
    (hij : i < j) (hjm : j < m) (haj : 0 < a j) :
    ∑ k ∈ Finset.range m, swapAlloc a i j k = ∑ k ∈ Finset.range m, a k := by
  have him : i < m := lt_trans hij hjm
  have hdi : ∑ x ∈ Finset.range m, (if x = i then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr him)
      (fun b _ hb => ite_eq_right hb)]
    exact ite_eq_left rfl
  have hdj : ∑ x ∈ Finset.range m, (if x = j then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hjm)
      (fun b _ hb => ite_eq_right hb)]
    exact ite_eq_left rfl
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

end CrownV
