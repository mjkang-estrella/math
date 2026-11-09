import CrownVSwapTotal

/-! Weighted-sum draft extracted from r23. Root changed only obsolete conditional names, Nat multiplication namespaces and a malformed sum binder. This copied draft is UNVERIFIED until the strict runner passes. -/

namespace CrownV

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
      (fun b _ hb => by rw [ite_eq_right hb, Nat.mul_zero])]
    simp
  have hwj : ∑ x ∈ Finset.range m, x * (if x = j then 1 else 0) = j := by
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hjm)
      (fun b _ hb => by rw [ite_eq_right hb, Nat.mul_zero])]
    simp
  have key : ∀ x ∈ Finset.range m,
      x * swapAlloc a i j x + x * (if x = j then 1 else 0)
        = x * a x + x * (if x = i then 1 else 0) := by
    intro x _
    have hs := swapAlloc_shift a i j x hij haj
    calc x * swapAlloc a i j x + x * (if x = j then 1 else 0)
        = x * (swapAlloc a i j x + (if x = j then 1 else 0)) := (Nat.mul_add x _ _).symm
      _ = x * (a x + (if x = i then 1 else 0)) := by rw [hs]
      _ = x * a x + x * (if x = i then 1 else 0) := Nat.mul_add x _ _
  have step : (∑ x ∈ Finset.range m, x * swapAlloc a i j x)
      + (∑ x ∈ Finset.range m, x * (if x = j then 1 else 0))
      = (∑ x ∈ Finset.range m, x * a x)
        + (∑ x ∈ Finset.range m, x * (if x = i then 1 else 0)) := by
    calc (∑ x ∈ Finset.range m, x * swapAlloc a i j x)
        + (∑ x ∈ Finset.range m, x * (if x = j then 1 else 0))
        = ∑ y ∈ Finset.range m,
            (y * swapAlloc a i j y + y * (if y = j then 1 else 0)) := by
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
