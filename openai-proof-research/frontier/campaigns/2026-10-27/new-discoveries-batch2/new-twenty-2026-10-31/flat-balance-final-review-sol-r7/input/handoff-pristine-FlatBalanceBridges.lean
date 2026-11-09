/-
MathDB 352972 generic source-fidelity bridges (R1).

Source: Hossein Teimoori Faal, "On Clique Roots of Flat Graphs", arXiv:2112.09721v1.
Companion to FlatBalance.lean (literal K_{3,3} refutation, source
4a4ca90e72d35f516ca4f84f9ab3fcb1e49527f5625278ed67ba2cabbeed889d).

This module proves, for ARBITRARY finite simple graphs (the empty vertex type
included), the generic translation bridges between the source's clique-count
conventions and the bounded Lean encodings:

  * `cliqueCount G 0 = 1`                (source global convention c_0 = 1)
  * `cliqueCount G k = 0` for `card V < k` (no cliques above the vertex count;
    the source's clique-count support is finite and bounded)
  * cutoff independence: the bounded parity sums are unchanged when the range
    is extended past `card V`, hence they equal the actual source odd/even
    totals over all k (finite support)
  * parity partition: odd sum + even sum = total clique sum; the positive-index
    even sum differs from the c_0-inclusive even sum exactly by c_0
  * the `Int.natAbs` discrepancy is the true integer, respectively real,
    absolute odd-minus-even difference, and `Balanced` (bound <= 1) agrees
    with the absolute-value bound over Z and over R
  * a graph with discrepancy > 1 is not balanced, and the literal
    `not_flat_balanced_conjecture` endpoint is re-derived through these
    generic bridges, so the bridges are formally connected to the acceptance
    endpoint rather than isolated lemmas.

No graph definition is weakened: `Flat`, `Balanced`, `cliqueCount` and the
parity sums are the unchanged definitions of `FlatBalance.lean`. No Nat
truncated subtraction carries an answer: all signed differences are formed in
Z before absolute values. No new axioms, sorry, admit, unsafe or native_decide.

Pins: Lean v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52),
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/

import FlatBalance
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Basic.Real.Basic

/-!
# MathDB 352972: generic finite-graph bridges for the flat balance conjecture
-/

namespace FlatBalance

/-! ## The `c_0 = 1` convention holds for every finite simple graph

The empty vertex type is included: the empty `Finset` is a clique of every
graph, and it is the unique clique of size zero. -/

/-- The 0-cliques of any finite simple graph are exactly the singleton
`{empty}`. -/
theorem cliqueFinset_zero {V : Type} [Fintype V] (G : SimpleGraph V) :
    cliqueFinset G 0 = {∅} := by
  ext s
  rw [mem_cliqueFinset, Finset.mem_singleton]
  constructor
  · intro h
    exact Finset.card_eq_zero.mp h.1
  · rintro rfl
    refine ⟨Finset.card_empty, fun a ha _ _ _ => absurd ha (Finset.notMem_empty a)⟩

/-- Generic `c_0 = 1`: every finite simple graph, the empty graph included,
has exactly one 0-clique. -/
theorem cliqueCount_zero {V : Type} [Fintype V] (G : SimpleGraph V) :
    cliqueCount G 0 = 1 := by
  show (cliqueFinset G 0).card = 1
  rw [cliqueFinset_zero, Finset.card_singleton]

/-! ## No cliques above the vertex count

Every `Finset` of `V` is a subset of `univ`, hence has at most `card V`
elements; the source's clique counts therefore have finite support contained
in `{0, ..., card V}`. -/

/-- The `k`-cliques are empty whenever `k` exceeds the vertex count. -/
theorem cliqueFinset_empty_of_card_lt {V : Type} [Fintype V] (G : SimpleGraph V)
    {k : ℕ} (hk : Fintype.card V < k) : cliqueFinset G k = ∅ := by
  ext s
  rw [mem_cliqueFinset]
  constructor
  · rintro ⟨hc, -⟩
    have h1 : s.card ≤ Fintype.card V := by
      calc s.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ s)
        _ = Fintype.card V := Finset.card_univ
    have hF : False := by omega
    exact hF.elim
  · intro hmem
    exact absurd hmem (Finset.notMem_empty s)

/-- Generic vanishing: `c_k(G) = 0` for every `k > card V`, for every finite
simple graph `G`. -/
theorem cliqueCount_of_card_lt {V : Type} [Fintype V] (G : SimpleGraph V)
    {k : ℕ} (hk : Fintype.card V < k) : cliqueCount G k = 0 := by
  show (cliqueFinset G k).card = 0
  rw [cliqueFinset_empty_of_card_lt G hk, Finset.card_empty]

/-! ## Finite support: the bounded sums do not depend on the cutoff

Any cutoff beyond `card V` adds only zero terms, for each parity selector. -/

/-- Range-extension lemma: if `f` vanishes above `n`, the sums over
`range (n+1+m)` and `range (n+1)` agree. -/
private theorem sum_range_cutoff (f : ℕ → ℕ) (n m : ℕ)
    (hzero : ∀ d, n < d → f d = 0) :
    ∑ d ∈ Finset.range (n + 1 + m), f d = ∑ d ∈ Finset.range (n + 1), f d := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hE : n + 1 + (k + 1) = (n + 1 + k) + 1 := by omega
    have hf : f (n + 1 + k) = 0 := hzero _ (by omega)
    rw [hE, Finset.sum_range_succ, ih, hf, add_zero]

/-- The odd clique sum is unchanged by any larger cutoff: its support is
exactly finite. -/
theorem oddCliqueSum_cutoff {V : Type} [Fintype V] (G : SimpleGraph V) {N : ℕ}
    (hN : Fintype.card V < N) :
    ∑ d ∈ Finset.range N, (if d % 2 = 1 then cliqueCount G d else 0)
      = oddCliqueSum G := by
  obtain ⟨m, hm⟩ : ∃ m, N = Fintype.card V + 1 + m :=
    ⟨N - (Fintype.card V + 1), by omega⟩
  rw [hm]
  have hz : ∀ d, Fintype.card V < d → (if d % 2 = 1 then cliqueCount G d else 0) = 0 := by
    intro d hlt
    rcases Nat.mod_two_eq_zero_or_one d with hh | hh
    · rw [ite_eq_right (show ¬(d % 2 = 1) by omega)]
    · rw [ite_eq_left hh]
      exact cliqueCount_of_card_lt G hlt
  calc ∑ d ∈ Finset.range (Fintype.card V + 1 + m),
        (if d % 2 = 1 then cliqueCount G d else 0)
      = ∑ d ∈ Finset.range (Fintype.card V + 1),
          (if d % 2 = 1 then cliqueCount G d else 0) := sum_range_cutoff _ _ _ hz
    _ = oddCliqueSum G := rfl

/-- The even clique sum (with `c_0`) is unchanged by any larger cutoff. -/
theorem evenCliqueSum_cutoff {V : Type} [Fintype V] (G : SimpleGraph V) {N : ℕ}
    (hN : Fintype.card V < N) :
    ∑ d ∈ Finset.range N, (if d % 2 = 0 then cliqueCount G d else 0)
      = evenCliqueSum G := by
  obtain ⟨m, hm⟩ : ∃ m, N = Fintype.card V + 1 + m :=
    ⟨N - (Fintype.card V + 1), by omega⟩
  rw [hm]
  have hz : ∀ d, Fintype.card V < d → (if d % 2 = 0 then cliqueCount G d else 0) = 0 := by
    intro d hlt
    rcases Nat.mod_two_eq_zero_or_one d with hh | hh
    · rw [ite_eq_left hh]
      exact cliqueCount_of_card_lt G hlt
    · rw [ite_eq_right (show ¬(d % 2 = 0) by omega)]
  calc ∑ d ∈ Finset.range (Fintype.card V + 1 + m),
        (if d % 2 = 0 then cliqueCount G d else 0)
      = ∑ d ∈ Finset.range (Fintype.card V + 1),
          (if d % 2 = 0 then cliqueCount G d else 0) := sum_range_cutoff _ _ _ hz
    _ = evenCliqueSum G := rfl

/-- The positive-index even sum is unchanged by any larger cutoff. -/
theorem evenCliqueSumPos_cutoff {V : Type} [Fintype V] (G : SimpleGraph V) {N : ℕ}
    (hN : Fintype.card V < N) :
    ∑ d ∈ Finset.range N, (if d % 2 = 0 ∧ 0 < d then cliqueCount G d else 0)
      = evenCliqueSumPos G := by
  obtain ⟨m, hm⟩ : ∃ m, N = Fintype.card V + 1 + m :=
    ⟨N - (Fintype.card V + 1), by omega⟩
  rw [hm]
  have hz : ∀ d, Fintype.card V < d →
      (if d % 2 = 0 ∧ 0 < d then cliqueCount G d else 0) = 0 := by
    intro d hlt
    rcases Nat.mod_two_eq_zero_or_one d with hh | hh
    · rw [ite_eq_left ⟨hh, by omega⟩]
      exact cliqueCount_of_card_lt G hlt
    · rw [ite_eq_right (show ¬(d % 2 = 0 ∧ 0 < d) by omega)]
  calc ∑ d ∈ Finset.range (Fintype.card V + 1 + m),
        (if d % 2 = 0 ∧ 0 < d then cliqueCount G d else 0)
      = ∑ d ∈ Finset.range (Fintype.card V + 1),
          (if d % 2 = 0 ∧ 0 < d then cliqueCount G d else 0) := sum_range_cutoff _ _ _ hz
    _ = evenCliqueSumPos G := rfl

/-! ## Parity partition of the total clique sum -/

/-- Pointwise: the odd- and even-selected parts of `c_d` reassemble to `c_d`. -/
private theorem iteOddAddEven (c d : ℕ) :
    (if d % 2 = 1 then c else 0) + (if d % 2 = 0 then c else 0) = c := by
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · rw [ite_eq_right (show ¬(d % 2 = 1) by omega), ite_eq_left h, Nat.zero_add]
  · rw [ite_eq_left h, ite_eq_right (show ¬(d % 2 = 0) by omega), Nat.add_zero]

/-- Source-total translation: the odd and even (`c_0` included) bounded sums
partition the total clique sum over `0, ..., card V`; since higher counts
vanish, this is exactly the source's odd/even split of the full clique-count
sequence. -/
theorem oddAddEvenCliqueSum {V : Type} [Fintype V] (G : SimpleGraph V) :
    oddCliqueSum G + evenCliqueSum G =
      ∑ d ∈ Finset.range (Fintype.card V + 1), cliqueCount G d := by
  calc oddCliqueSum G + evenCliqueSum G
      = ∑ d ∈ Finset.range (Fintype.card V + 1), (if d % 2 = 1 then cliqueCount G d else 0) +
        ∑ d ∈ Finset.range (Fintype.card V + 1), (if d % 2 = 0 then cliqueCount G d else 0) := by
        unfold oddCliqueSum evenCliqueSum
        rfl
    _ = ∑ d ∈ Finset.range (Fintype.card V + 1),
          ((if d % 2 = 1 then cliqueCount G d else 0) +
            (if d % 2 = 0 then cliqueCount G d else 0)) := Finset.sum_add_distrib.symm
    _ = ∑ d ∈ Finset.range (Fintype.card V + 1), cliqueCount G d :=
        Finset.sum_congr rfl fun _ _ => iteOddAddEven _ _

/-- Pointwise: the even term splits into its positive part and the size-zero
part. -/
private theorem iteEvenSplit (c d : ℕ) :
    (if d % 2 = 0 then c else 0)
      = (if d = 0 then c else 0) + (if d % 2 = 0 ∧ 0 < d then c else 0) := by
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · rcases Nat.lt_or_ge d 1 with hd | hd
    · rw [ite_eq_left h, ite_eq_left (show d = 0 by omega),
        ite_eq_right (show ¬(d % 2 = 0 ∧ 0 < d) by omega), Nat.add_zero]
    · rw [ite_eq_left h, ite_eq_left (show d % 2 = 0 ∧ 0 < d by exact ⟨h, by omega⟩), ite_eq_right (show ¬(d = 0) by omega), Nat.zero_add]
  · rw [ite_eq_right (show ¬(d % 2 = 0) by omega), ite_eq_right (show ¬(d = 0) by omega),
      ite_eq_right (show ¬(d % 2 = 0 ∧ 0 < d) by omega), Nat.zero_add]

/-- The sum of the size-zero selectors is the size-zero count. -/
private theorem sum_zeroDelta (f : ℕ → ℕ) (n : ℕ) :
    ∑ d ∈ Finset.range (n + 1), (if d = 0 then f d else 0) = f 0 := by
  induction n with
  | zero =>
    rw [Finset.sum_range_succ]
    show (∑ d ∈ Finset.range 0, (if d = 0 then f d else 0)) +
      (if (0 : ℕ) = 0 then f 0 else 0) = f 0
    rw [Finset.sum_range_zero, ite_eq_left (show (0 : ℕ) = 0 by rfl), Nat.zero_add]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    show (∑ d ∈ Finset.range (k + 1), (if d = 0 then f d else 0)) +
      (if (k : ℕ) + 1 = 0 then f (k + 1) else 0) = f 0
    rw [ih, ite_eq_right (show ¬((k : ℕ) + 1 = 0) by omega), add_zero]

/-- Convention separation: the `c_0`-inclusive even sum is exactly the
positive-index even sum plus `c_0`. The two source conventions stay distinct
objects; neither is substituted for the other. -/
theorem evenCliqueSum_decomp {V : Type} [Fintype V] (G : SimpleGraph V) :
    evenCliqueSum G = cliqueCount G 0 + evenCliqueSumPos G := by
  have hdelta : ∑ d ∈ Finset.range (Fintype.card V + 1),
      (if d = 0 then cliqueCount G d else 0) = cliqueCount G 0 :=
    sum_zeroDelta _ _
  calc evenCliqueSum G
      = ∑ d ∈ Finset.range (Fintype.card V + 1),
          ((if d = 0 then cliqueCount G d else 0) +
            (if d % 2 = 0 ∧ 0 < d then cliqueCount G d else 0)) := by
        unfold evenCliqueSum
        exact Finset.sum_congr rfl fun _ _ => iteEvenSplit _ _
    _ = (∑ d ∈ Finset.range (Fintype.card V + 1), (if d = 0 then cliqueCount G d else 0)) +
        ∑ d ∈ Finset.range (Fintype.card V + 1),
          (if d % 2 = 0 ∧ 0 < d then cliqueCount G d else 0) := Finset.sum_add_distrib
    _ = cliqueCount G 0 + ∑ d ∈ Finset.range (Fintype.card V + 1),
          (if d % 2 = 0 ∧ 0 < d then cliqueCount G d else 0) := by rw [hdelta]
    _ = cliqueCount G 0 + evenCliqueSumPos G := by unfold evenCliqueSumPos; rfl

/-! ## Exact integer and real casts of the discrepancy -/

/-- The integer cast of `Int.natAbs z` is the true absolute value of `z` in
`Z`; no truncated natural subtraction is involved anywhere. -/
theorem natAbs_cast_abs (z : ℤ) : (Int.natAbs z : ℤ) = |z| :=
  Int.natCast_natAbs z

/-- The integer cast of the clique-count discrepancy is the exact integer
absolute difference of the odd and even clique sums. -/
theorem discrepancyNat_cast_int {V : Type} [Fintype V] (G : SimpleGraph V) :
    (discrepancyNat G : ℤ) = |(oddCliqueSum G : ℤ) - (evenCliqueSum G : ℤ)| :=
  Int.natCast_natAbs _

/-- For naturals, the real cast of the `natAbs` difference is the real
absolute difference. -/
theorem natAbs_cast_real (a b : ℕ) :
    (Nat.cast (Int.natAbs ((a : ℤ) - (b : ℤ))) : ℝ)
      = |(Nat.cast a : ℝ) - (Nat.cast b : ℝ)| := by
  have h1 : (Int.natAbs ((a : ℤ) - (b : ℤ)) : ℤ) = |(a : ℤ) - (b : ℤ)| :=
    Int.natCast_natAbs _
  have h2 : (Nat.cast (Int.natAbs ((a : ℤ) - (b : ℤ))) : ℝ)
      = (Int.cast (Int.natAbs ((a : ℤ) - (b : ℤ))) : ℝ) :=
    (Int.cast_natCast _).symm
  have h3 : (Int.cast (Int.natAbs ((a : ℤ) - (b : ℤ))) : ℝ)
      = (Int.cast |(a : ℤ) - (b : ℤ)| : ℝ) := by
    rw [h1]
  have h4 : (Int.cast |(a : ℤ) - (b : ℤ)| : ℝ)
      = |(Int.cast ((a : ℤ) - (b : ℤ)) : ℝ)| := by
    rw [Int.cast_abs]
  have h5 : (Int.cast ((a : ℤ) - (b : ℤ)) : ℝ)
      = (Nat.cast a : ℝ) - (Nat.cast b : ℝ) := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  calc (Nat.cast (Int.natAbs ((a : ℤ) - (b : ℤ))) : ℝ)
      = (Int.cast (Int.natAbs ((a : ℤ) - (b : ℤ))) : ℝ) := h2
    _ = (Int.cast |(a : ℤ) - (b : ℤ)| : ℝ) := h3
    _ = |(Int.cast ((a : ℤ) - (b : ℤ)) : ℝ)| := h4
    _ = |(Nat.cast a : ℝ) - (Nat.cast b : ℝ)| := by rw [h5]

/-- The real cast of the clique-count discrepancy is the exact real absolute
difference of the odd and even clique sums. -/
theorem discrepancyNat_cast_real {V : Type} [Fintype V] (G : SimpleGraph V) :
    (Nat.cast (discrepancyNat G) : ℝ)
      = |(Nat.cast (oddCliqueSum G) : ℝ) - (Nat.cast (evenCliqueSum G) : ℝ)| := by
  have h := natAbs_cast_real (oddCliqueSum G) (evenCliqueSum G)
  exact h

/-- Bound equivalence over the integers: `Balanced` (discrepancy at most one)
agrees with the absolute-value bound in `Z`. -/
theorem balanced_iff_absInt {V : Type} [Fintype V] (G : SimpleGraph V) :
    Balanced G ↔ |(oddCliqueSum G : ℤ) - (evenCliqueSum G : ℤ)| ≤ 1 := by
  constructor
  · intro hbal
    have h : Int.natAbs ((oddCliqueSum G : ℤ) - (evenCliqueSum G : ℤ)) ≤ 1 := hbal
    have h2 : ((Int.natAbs ((oddCliqueSum G : ℤ) - (evenCliqueSum G : ℤ)) : ℕ) : ℤ) ≤ 1 := by
      omega
    rw [Int.natCast_natAbs] at h2
    exact h2
  · intro h
    have h2 : ((Int.natAbs ((oddCliqueSum G : ℤ) - (evenCliqueSum G : ℤ)) : ℕ) : ℤ) ≤ 1 := by
      rw [Int.natCast_natAbs]; exact h
    have h3 : Int.natAbs ((oddCliqueSum G : ℤ) - (evenCliqueSum G : ℤ)) ≤ 1 := by omega
    exact h3

/-- Bound equivalence over the reals. -/
theorem balanced_iff_absReal {V : Type} [Fintype V] (G : SimpleGraph V) :
    Balanced G
      ↔ |(Nat.cast (oddCliqueSum G) : ℝ) - (Nat.cast (evenCliqueSum G) : ℝ)| ≤ 1 := by
  constructor
  · intro hbal
    have h : discrepancyNat G ≤ 1 := hbal
    have h1 : (Nat.cast (discrepancyNat G) : ℝ) ≤ 1 := Nat.cast_le_one.mpr h
    rw [discrepancyNat_cast_real] at h1
    exact h1
  · intro h
    have h1 : (Nat.cast (discrepancyNat G) : ℝ) ≤ 1 := by
      rw [discrepancyNat_cast_real]; exact h
    have h2 : discrepancyNat G ≤ 1 := Nat.cast_le_one.mp h1
    exact h2

/-- A finite simple graph whose clique-count discrepancy exceeds one is not
balanced; this is the generic contrapositive bridge used at the endpoint. -/
theorem not_balanced_of_one_lt_discrepancy {V : Type} [Fintype V]
    {G : SimpleGraph V} (h : 1 < discrepancyNat G) : ¬ Balanced G := by
  intro hbal
  have h1 : discrepancyNat G ≤ 1 := hbal
  omega

/-- Source-level endpoint through the generic bridges: the explicit finite
counterexample, with its non-balance obtained from `K33_discrepancy_gt_one`
via the generic bridge `not_balanced_of_one_lt_discrepancy` rather than from
a witness-specific lemma. -/
theorem flat_not_balanced_exists_via_bridges :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      @Flat V _ G ∧ ¬ @Balanced V _ G :=
  ⟨Fin 3 ⊕ Fin 3, inferInstance, K33, K33_flat,
    not_balanced_of_one_lt_discrepancy (V := Fin 3 ⊕ Fin 3) (G := K33)
      K33_discrepancy_gt_one⟩

/-- The literal refutation, re-derived through the generic bridges. -/
theorem not_flat_balanced_conjecture_via_bridges : ¬ FlatBalancedConjecture := by
  intro Hall
  obtain ⟨V, hV, G, hflat, hnb⟩ := flat_not_balanced_exists_via_bridges
  exact hnb (Hall V hV G hflat)

end FlatBalance
