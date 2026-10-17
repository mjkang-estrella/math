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

/-- The exact S2 choice m=n²+2 gives the uniform negative total −m. -/
theorem aggregate_negative {α : Type*} [DecidableEq α]
    (I S : Finset α) (f : α → ℤ) (n m : ℤ)
    (hSI : S ⊆ I) (hm : m = n^2 + 2)
    (hCard : (I.card : ℤ) = n * m) (hMany : m - 1 ≤ (S.card : ℤ))
    (hBase : ∀ i ∈ I \ S, f i ≤ n)
    (hSpecial : ∀ i ∈ S, f i ≤ n - m) :
    (∑ i ∈ I, f i ≤ -m) ∧ (∑ i ∈ I, f i < 0) := by
  have hmpos : 0 < m := by nlinarith [sq_nonneg n]
  have h := aggregate_bound I S f n m hSI (le_of_lt hmpos) hCard hMany hBase hSpecial
  have hid : n^2 * m - m * (m - 1) = -m := by rw [hm]; ring
  rw [hid] at h
  constructor
  · exact h
  · omega

/-- Sum the actual fiber cardinality defects. This does not identify those
sums with coordinate-image cardinalities; that fiber decomposition is prose. -/
theorem fiber_cardinality_strict {α β : Type*} [DecidableEq α]
    (I : Finset α) (A B C : α → Finset β)
    (h : (∑ i ∈ I, (((A i).card : ℤ) + ((C i).card : ℤ) -
      2 * ((B i).card : ℤ))) < 0) :
    (∑ i ∈ I, ((A i).card : ℤ)) + (∑ i ∈ I, ((C i).card : ℤ)) <
      2 * (∑ i ∈ I, ((B i).card : ℤ)) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum] at h ⊢
  omega

/-- Actual disjoint indexed-fiber cardinalities, via the sigma construction.
Each fiber is tagged by its index, exactly as a column or row in a product. -/
theorem fiber_sigma_strict {α β : Type*} [DecidableEq α]
    (I : Finset α) (A B C : α → Finset β)
    (h : (∑ i ∈ I, (((A i).card : ℤ) + ((C i).card : ℤ) -
      2 * ((B i).card : ℤ))) < 0) :
    (I.sigma A).card + (I.sigma C).card < 2 * (I.sigma B).card := by
  have hs := fiber_cardinality_strict I A B C h
  simp only [Finset.card_sigma]
  exact_mod_cast hs

/-- Cardinality complement gain from two strict coordinate-image inequalities.
All sets live in the finite ambient U; old images are disjoint. -/
theorem complement_gain {α : Type*} [DecidableEq α]
    (U P Q JP JQ JJP JJQ : Finset α)
    (hJP : JP ⊆ U) (hJQ : JQ ⊆ U) (hJJP : JJP ⊆ U) (hJJQ : JJQ ⊆ U)
    (hdis : Disjoint JP JQ)
    (hP : P.card + JJP.card < 2 * JP.card)
    (hQ : Q.card + JJQ.card < 2 * JQ.card) :
    P.card + Q.card + 2 * (U \ (JP ∪ JQ)).card <
      (U \ JJQ).card + (U \ JJP).card := by
  have hu : JP ∪ JQ ⊆ U := Finset.union_subset hJP hJQ
  have hd := Finset.card_sdiff_add_card_eq_card hu
  have hr := Finset.card_sdiff_add_card_eq_card hJJQ
  have hc := Finset.card_sdiff_add_card_eq_card hJJP
  have hj := Finset.card_union_of_disjoint hdis
  omega

/-- Quantified cardinality part of pruning. The existence, compatibility,
retained diagonal, and deletion guarantee are not proved by this lemma. -/
theorem pruning_objective_gain {α : Type*} [DecidableEq α]
    (R C P' Q' : Finset α) (M d d' : ℕ)
    (hP : P' ⊆ R) (hQ : Q' ⊆ C)
    (hGain : M + 2*d < R.card + C.card)
    (hDelete : (R \ P').card + (C \ Q').card ≤ d + d') :
    M + d < P'.card + Q'.card + d' := by
  have hp := Finset.card_sdiff_add_card_eq_card hP
  have hq := Finset.card_sdiff_add_card_eq_card hQ
  omega

/-- The whole finite-set numerical closure, assuming an actual output of the
pruning lemma and the asserted objective maximality. No graph claim is hidden. -/
theorem complement_pruning_contradiction {α : Type*} [DecidableEq α]
    (U P Q JP JQ JJP JJQ P' Q' : Finset α) (d' : ℕ)
    (hJP : JP ⊆ U) (hJQ : JQ ⊆ U) (hJJP : JJP ⊆ U) (hJJQ : JJQ ⊆ U)
    (hdis : Disjoint JP JQ)
    (hP : P.card + JJP.card < 2 * JP.card)
    (hQ : Q.card + JJQ.card < 2 * JQ.card)
    (hP' : P' ⊆ U \ JJQ) (hQ' : Q' ⊆ U \ JJP)
    (hDelete : ((U \ JJQ) \ P').card + ((U \ JJP) \ Q').card ≤
      (U \ (JP ∪ JQ)).card + d')
    (hMax : P'.card + Q'.card + d' ≤
      P.card + Q.card + (U \ (JP ∪ JQ)).card) : False := by
  have hGain := complement_gain U P Q JP JQ JJP JJQ hJP hJQ hJJP hJJQ hdis hP hQ
  have hFinal := pruning_objective_gain (U \ JJQ) (U \ JJP) P' Q'
    (P.card + Q.card) (U \ (JP ∪ JQ)).card d' hP' hQ' hGain hDelete
  omega

end SeymourSupport
