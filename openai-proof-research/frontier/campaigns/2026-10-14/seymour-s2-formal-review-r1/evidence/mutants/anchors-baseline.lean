/- Copyright 2026 Myeongjin Kang. Licensed under MIT.
Supporting finite-set and integer lemmas for the S2 proof. Not the graph theorem.
-/
import Mathlib

open scoped BigOperators
namespace SeymourSupport

/-- The exact boundary identity yields the weak deficit. The identity and
indicator bounds are explicit inputs, not graph facts proved here. -/
theorem boundary_weak (dD dH a q b : ℤ)
    (hId : dD = dH + q + b - a) (hD : dD ≤ -1)
    (ha : a ≤ 1) (hq : 0 ≤ q) (hb : 0 ≤ b) : dH ≤ 0 := by
  omega

/-- Avoiding the successor ensures q ≥ a, giving strictness. -/
theorem boundary_strict (dD dH a q b : ℤ)
    (hId : dD = dH + q + b - a) (hD : dD ≤ -1)
    (haq : a ≤ q) (hb : 0 ≤ b) : dH ≤ -1 := by
  omega

/-- Complete Boolean case split for the indicators used in candidate §3.
`hits` means z is in F_D(S), `avoids` means w is outside F(S) ∪ F²(S),
`returns` means z is in F_D(F(S)). The graph-to-identity step is assumed. -/
theorem boundary_indicators (dD dH : ℤ) (hits avoids returns : Prop)
    [Decidable hits] [Decidable avoids] [Decidable returns]
    (hId : dD = dH + (if hits ∧ avoids then 1 else 0) +
      (if ¬hits ∧ returns then 1 else 0) - (if hits then 1 else 0))
    (hD : dD ≤ -1) : dH ≤ 0 ∧ (avoids → dH ≤ -1) := by
  by_cases hh : hits <;> by_cases hw : avoids <;> by_cases hr : returns <;>
    simp_all <;> omega

/-- Sum bounds for an arbitrary finite family with a distinguished subset.
No independence or disjointness of the values is required. -/
theorem sum_with_specials {α : Type*} [DecidableEq α]
    (I S : Finset α) (f : α → ℤ) (n m : ℤ)
    (hSI : S ⊆ I)
    (hBase : ∀ i ∈ I \ S, f i ≤ n)
    (hSpecial : ∀ i ∈ S, f i ≤ n - m) :
    ∑ i ∈ I, f i ≤ (I.card : ℤ) * n - (S.card : ℤ) * m := by
  have h0 : ∑ i ∈ I \ S, f i ≤ ((I \ S).card : ℤ) * n := by
    simpa using Finset.sum_le_sum hBase
  have h1 : ∑ i ∈ S, f i ≤ (S.card : ℤ) * (n - m) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hSpecial
  have hc : ((I \ S).card : ℤ) + (S.card : ℤ) = (I.card : ℤ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hSI
  have hs := Finset.sum_sdiff hSI (f := f)
  calc
    ∑ i ∈ I, f i = (∑ i ∈ I \ S, f i) + ∑ i ∈ S, f i := hs.symm
    _ ≤ ((I \ S).card : ℤ) * n + (S.card : ℤ) * (n - m) := add_le_add h0 h1
    _ = (I.card : ℤ) * n - (S.card : ℤ) * m := by rw [← hc]; ring

/-- The m−1 special fibers may be a lower bound, not an exact count. -/
theorem aggregate_bound {α : Type*} [DecidableEq α]
    (I S : Finset α) (f : α → ℤ) (n m : ℤ)
    (hSI : S ⊆ I) (hm : 0 ≤ m)
    (hCard : (I.card : ℤ) = n * m) (hMany : m - 1 ≤ (S.card : ℤ))
    (hBase : ∀ i ∈ I \ S, f i ≤ n)
    (hSpecial : ∀ i ∈ S, f i ≤ n - m) :
    ∑ i ∈ I, f i ≤ n^2 * m - m * (m - 1) := by
  have h := sum_with_specials I S f n m hSI hBase hSpecial
  have ht := mul_le_mul_of_nonneg_right hMany hm
  rw [hCard] at h
  nlinarith

end SeymourSupport
