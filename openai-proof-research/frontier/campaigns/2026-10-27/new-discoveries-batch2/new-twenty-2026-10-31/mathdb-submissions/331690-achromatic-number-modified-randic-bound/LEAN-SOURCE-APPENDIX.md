# Lean source appendix

Modules are listed in import order.

## AchDefs.lean

```lean
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

/-!
# Definitions for MathDB 331690

Wu and Elphick (arXiv:1511.00537, Conjecture 4.1): for any graph `G`,
`ψ(G) ≤ 2 R'(G)`, where `R'(G) = ∑_{uv ∈ E(G)} 1 / max (d(u), d(v))` and `ψ(G)` is the
achromatic number, the maximum `k` for which `G` has a complete `k`-colouring.

This file fixes the definitions and proves that `2 R'(G)` equals the sum of the weights
`1 / max (d(u), d(v))` over ordered pairs of adjacent vertices.
-/

namespace Ach331690

open Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The weight `1 / max (d(u), d(v))` of the pair `u, v`. -/
def wt (u v : V) : ℚ := 1 / ((max (G.degree u) (G.degree v) : ℕ) : ℚ)

theorem wt_comm (u v : V) : wt G u v = wt G v u := by
  simp only [wt, max_comm]

/-- The index `R'(G) = ∑_{uv ∈ E(G)} 1 / max (d(u), d(v))` of Dvořák, Lidický and
Škrekovski, as defined by Wu and Elphick: a sum over the unordered edges of `G`. -/
def randicPrime : ℚ :=
  ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => wt G u v, wt_comm G⟩ e

/-- A colouring `c : V → Fin k` is *complete* if for each pair of different colours there
are adjacent vertices with these colours. -/
def IsCompleteColouring {k : ℕ} (c : V → Fin k) : Prop :=
  ∀ i j : Fin k, i ≠ j → ∃ u v, G.Adj u v ∧ c u = i ∧ c v = j

/-- A colouring is *proper* if adjacent vertices receive different colours. -/
def IsProperColouring {k : ℕ} (c : V → Fin k) : Prop :=
  ∀ u v, G.Adj u v → c u ≠ c v

/-- `G` has a complete proper `k`-colouring: a proper colouring using all `k` colours in
which every two different colours are joined by an edge. -/
def HasCompleteColouring (k : ℕ) : Prop :=
  ∃ c : V → Fin k, Function.Surjective c ∧ IsProperColouring G c ∧ IsCompleteColouring G c

/-- `G` has a complete `k`-pseudocolouring (properness dropped). -/
def HasCompletePseudoColouring (k : ℕ) : Prop :=
  ∃ c : V → Fin k, Function.Surjective c ∧ IsCompleteColouring G c

open Classical in
/-- The achromatic number `ψ(G)`: the maximum `k` for which `G` has a complete proper
`k`-colouring.  Such a `k` is at most `|V|`; the maximum exists by
`hasCompleteColouring_achromatic`. -/
noncomputable def achromatic : ℕ :=
  Nat.findGreatest (fun k => HasCompleteColouring G k) (Fintype.card V)

open Classical in
/-- The pseudoachromatic number: the maximum `k` for which `G` has a complete
`k`-pseudocolouring. -/
noncomputable def pseudoachromatic : ℕ :=
  Nat.findGreatest (fun k => HasCompletePseudoColouring G k) (Fintype.card V)

/-- Regrouping: `2 R'(G)` is the sum of `wt` over ordered pairs of adjacent vertices. -/
theorem two_mul_randicPrime :
    2 * randicPrime G = ∑ u, ∑ v, if G.Adj u v then wt G u v else 0 := by
  classical
  have h1 : ∑ d : G.Dart, wt G d.fst d.snd = 2 * randicPrime G := by
    unfold randicPrime
    rw [Finset.mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := G.edgeFinset)
      (g := fun d : G.Dart => d.edge) (fun d _ => by simp)]
    refine Finset.sum_congr rfl fun e he => ?_
    have hc : ∀ d ∈ ({d : G.Dart | d.edge = e} : Finset G.Dart),
        wt G d.fst d.snd = Sym2.lift ⟨fun u v => wt G u v, wt_comm G⟩ e := by
      intro d hd
      rw [mem_filter] at hd
      rw [← hd.2]
      rfl
    rw [Finset.sum_congr rfl hc, sum_const, G.dart_edge_fiber_card e (SimpleGraph.mem_edgeFinset.1 he)]
    simp
  have h2 : ∑ d : G.Dart, wt G d.fst d.snd =
      ∑ p ∈ (univ.filter fun p : V × V => G.Adj p.1 p.2), wt G p.1 p.2 := by
    refine Finset.sum_bij' (fun d _ => (d.fst, d.snd)) (fun p h => ⟨p, (mem_filter.1 h).2⟩)
      ?_ ?_ ?_ ?_ ?_ <;> simp
  rw [← h1, h2, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

theorem randicPrime_nonneg : 0 ≤ randicPrime G := by
  have h := two_mul_randicPrime G
  have : 0 ≤ ∑ u, ∑ v, if G.Adj u v then wt G u v else 0 := by
    refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => ?_
    split_ifs
    · unfold wt; positivity
    · exact le_refl 0
  linarith

/-- An edgeless graph has `R' = 0`. -/
theorem randicPrime_eq_zero_of_edgeless (h : ∀ u v, ¬ G.Adj u v) : randicPrime G = 0 := by
  have h2 := two_mul_randicPrime G
  simp only [h, ite_false, sum_const_zero] at h2
  linarith

end Ach331690
```

## AchBound.lean

```lean
import AchDefs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Every complete colouring with `k` colours has `k ≤ 2 R'(G)` (graphs with an edge)

Main argument (`two_le_card_bound`): for `k ≥ 2` and a complete (pseudo)colouring
`c : V → Fin k`, put `t = k - 1`.  Choose a set `H` of at most `k` vertices of degree `≥ t`
such that every vertex of `H` has degree at least that of every vertex outside `H`, and
such that if `|H| < k` then every vertex outside `H` has degree `< t`.  A pointwise lower
bound for the weights of ordered adjacent pairs, summed, gives `2 R'(G) ≥ k`.
-/

namespace Ach331690

open Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem wt_of_le {u v : V} (h : G.degree v ≤ G.degree u) :
    wt G u v = 1 / (G.degree u : ℚ) := by
  simp [wt, max_eq_left h]

theorem wt_of_ge {u v : V} (h : G.degree u ≤ G.degree v) :
    wt G u v = 1 / (G.degree v : ℚ) := by
  simp [wt, max_eq_right h]

/-- The charges `1 / d(u)` on the edges at a vertex `u` of positive degree add up to `1`. -/
theorem sum_adj_inv_degree (u : V) (hu : G.degree u ≠ 0) :
    ∑ v, (if G.Adj u v then (1 : ℚ) / (G.degree u : ℚ) else 0) = 1 := by
  rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  rw [← G.neighborFinset_eq_filter (v := u), G.card_neighborFinset_eq_degree]
  have : (G.degree u : ℚ) ≠ 0 := by exact_mod_cast hu
  field_simp

variable [DecidableEq V]

/-- The pointwise lower bound `L(u,v) ≤ D(u,v)` for the weight `D(u,v)` of an ordered pair. -/
theorem pointwise_bound {k t : ℕ} (c : V → Fin k) (H : Finset V) (U : Finset (Fin k))
    (ht : 1 ≤ t) (P1 : ∀ u ∈ H, t ≤ G.degree u)
    (P2 : ∀ u ∈ H, ∀ v ∉ H, G.degree v ≤ G.degree u)
    (P3 : H.card < k → ∀ v ∉ H, G.degree v ≤ t)
    (hUout : ∀ u, c u ∈ U → u ∉ H) (u v : V) :
    (if u ∈ H ∧ G.Adj u v then 1 / (G.degree u : ℚ) else 0) +
      (if v ∈ H ∧ G.Adj u v then 1 / (G.degree v : ℚ) else 0) -
      (if u ∈ H ∧ v ∈ H ∧ G.Adj u v then 1 / (t : ℚ) else 0) +
      (if H.card < k ∧ G.Adj u v ∧ c u ∈ U ∧ c v ∈ U then 1 / (t : ℚ) else 0) ≤
    (if G.Adj u v then wt G u v else 0) := by
  have htq : (0 : ℚ) < t := by exact_mod_cast ht
  by_cases hadj : G.Adj u v
  · have hdu : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).2 ⟨v, hadj⟩
    have hdv : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).2 ⟨u, hadj.symm⟩
    by_cases hu : u ∈ H <;> by_cases hv : v ∈ H
    · have hcu : c u ∉ U := fun h => hUout u h hu
      simp only [hadj, hu, hv, hcu, and_true, and_false, false_and, ite_true,
        ite_false, add_zero]
      have h1 : 1 / (G.degree u : ℚ) ≤ 1 / (t : ℚ) :=
        one_div_le_one_div_of_le htq (by exact_mod_cast P1 u hu)
      have h2 : 1 / (G.degree v : ℚ) ≤ 1 / (t : ℚ) :=
        one_div_le_one_div_of_le htq (by exact_mod_cast P1 v hv)
      rcases le_total (G.degree u) (G.degree v) with h | h
      · rw [wt_of_ge G h]; linarith
      · rw [wt_of_le G h]; linarith
    · have hcu : c u ∉ U := fun h => hUout u h hu
      simp only [hadj, hu, hv, hcu, and_true, and_false, false_and, ite_true,
        ite_false, add_zero, sub_zero]
      rw [wt_of_le G (P2 u hu v hv)]
    · have hcv : c v ∉ U := fun h => hUout v h hv
      simp only [hadj, hu, hv, hcv, and_true, and_false, ite_true,
        ite_false, add_zero, sub_zero, zero_add]
      rw [wt_of_ge G (P2 v hv u hu)]
    · simp only [hadj, hu, hv, true_and, false_and, and_false, ite_true, ite_false,
        add_zero, sub_zero, zero_add]
      split_ifs with h4
      · obtain ⟨hlt, -, -⟩ := h4
        unfold wt
        have hmax : max (G.degree u) (G.degree v) ≤ t := max_le (P3 hlt u hu) (P3 hlt v hv)
        have hmpos : 0 < max (G.degree u) (G.degree v) := lt_max_of_lt_left hdu
        exact one_div_le_one_div_of_le (by exact_mod_cast hmpos) (by exact_mod_cast hmax)
      · unfold wt; positivity
  · simp [hadj]

/-- The degree-threshold set `H` of the proof. -/
theorem exists_threshold_set (k t : ℕ) :
    ∃ H : Finset V, H.card ≤ k ∧ (∀ u ∈ H, t ≤ G.degree u) ∧
      (∀ u ∈ H, ∀ v ∉ H, G.degree v ≤ G.degree u) ∧
      (H.card < k → ∀ v ∉ H, G.degree v < t) := by
  set S := (univ.filter fun v => t ≤ G.degree v) with hS
  set m := min k S.card with hm
  obtain ⟨H, hHmem, hHmax⟩ := Finset.exists_max_image (S.powersetCard m)
    (fun H => ∑ v ∈ H, G.degree v) (Finset.powersetCard_nonempty.2 (min_le_right _ _))
  rw [Finset.mem_powersetCard] at hHmem
  obtain ⟨hHS, hHcard⟩ := hHmem
  have P1 : ∀ u ∈ H, t ≤ G.degree u := fun u hu => (mem_filter.1 (hHS hu)).2
  refine ⟨H, ?_, P1, ?_, ?_⟩
  · rw [hHcard]; exact min_le_left _ _
  · intro u hu v hv
    by_contra hlt
    rw [not_le] at hlt
    by_cases hvS : v ∈ S
    · have hvn : v ∉ H.erase u := fun h => hv (mem_of_mem_erase h)
      have hmem : insert v (H.erase u) ∈ S.powersetCard m := by
        rw [mem_powersetCard]
        constructor
        · intro x hx
          rw [mem_insert] at hx
          rcases hx with rfl | hx
          · exact hvS
          · exact hHS (mem_of_mem_erase hx)
        · rw [card_insert_of_notMem hvn, card_erase_of_mem hu]
          have := card_pos.2 ⟨u, hu⟩
          omega
      have h1 := hHmax _ hmem
      rw [sum_insert hvn] at h1
      have h2 := Finset.add_sum_erase H (fun v => G.degree v) hu
      simp only at h1 h2
      omega
    · have h1 : ¬ t ≤ G.degree v := fun h => hvS (mem_filter.2 ⟨mem_univ _, h⟩)
      have := P1 u hu
      omega
  · intro hlt v hv
    have hHeq : H = S := Finset.eq_of_subset_of_card_le hHS (by omega)
    by_contra hge
    rw [not_lt] at hge
    exact hv (hHeq ▸ mem_filter.2 ⟨mem_univ _, hge⟩)

/-- **Main lemma.**  If `k ≥ 2` and `c : V → Fin k` is a complete colouring (adjacent
vertices may share a colour), then `k ≤ 2 R'(G)`. -/
theorem two_le_card_bound {k : ℕ} (hk : 2 ≤ k) (c : V → Fin k)
    (hc : IsCompleteColouring G c) : (k : ℚ) ≤ 2 * randicPrime G := by
  set t : ℕ := k - 1 with ht
  have ht1 : 1 ≤ t := by omega
  have htq : (t : ℚ) = k - 1 := by
    rw [ht, Nat.cast_sub (by omega)]
    simp
  have htpos : (0 : ℚ) < t := by exact_mod_cast ht1
  obtain ⟨H, hHk, P1, P2, P3⟩ := exists_threshold_set G k t
  set U : Finset (Fin k) := univ \ H.image c with hU
  have hUcard : k - H.card ≤ U.card := by
    have h1 : U.card = k - (H.image c).card := by
      rw [hU, card_univ_sdiff, Fintype.card_fin]
    have h2 := card_image_le (s := H) (f := c)
    omega
  have hUout : ∀ u, c u ∈ U → u ∉ H := fun u hu huH =>
    (mem_sdiff.1 hu).2 (mem_image_of_mem c huH)
  have P3' : H.card < k → ∀ v ∉ H, G.degree v ≤ t := fun h v hv => (P3 h v hv).le
  -- the four pieces of the lower bound
  have hS1 : ∑ u, ∑ v, (if u ∈ H ∧ G.Adj u v then 1 / (G.degree u : ℚ) else 0) = H.card := by
    have : ∀ u, ∑ v, (if u ∈ H ∧ G.Adj u v then 1 / (G.degree u : ℚ) else 0) =
        if u ∈ H then 1 else 0 := by
      intro u
      by_cases hu : u ∈ H
      · simp only [hu, true_and, ite_true]
        exact sum_adj_inv_degree G u (by have := P1 u hu; omega)
      · simp [hu]
    rw [Finset.sum_congr rfl (fun u _ => this u)]
    simp
  have hS2 : ∑ u, ∑ v, (if v ∈ H ∧ G.Adj u v then 1 / (G.degree v : ℚ) else 0) = H.card := by
    rw [Finset.sum_comm, ← hS1]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
    simp only [G.adj_comm u v]
  have hS3 : (∑ u, ∑ v, (if u ∈ H ∧ v ∈ H ∧ G.Adj u v then 1 / (t : ℚ) else 0)) * t ≤
      (H.card : ℚ) * (H.card - 1) := by
    have hper : ∀ u, (∑ v, (if u ∈ H ∧ v ∈ H ∧ G.Adj u v then 1 / (t : ℚ) else 0)) * t ≤
        if u ∈ H then (H.card : ℚ) - 1 else 0 := by
      intro u
      by_cases hu : u ∈ H
      · simp only [hu, true_and, ite_true]
        rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
        have hsub : (univ.filter fun v => v ∈ H ∧ G.Adj u v) ⊆ H.erase u := by
          intro v hv
          rw [mem_filter] at hv
          exact mem_erase.2 ⟨(G.ne_of_adj hv.2.2).symm, hv.2.1⟩
        have hc1 : (univ.filter fun v => v ∈ H ∧ G.Adj u v).card + 1 ≤ H.card := by
          have := card_le_card hsub
          have := card_erase_of_mem hu
          have := card_pos.2 ⟨u, hu⟩
          omega
        have hc2 : ((univ.filter fun v => v ∈ H ∧ G.Adj u v).card : ℚ) + 1 ≤ H.card := by
          exact_mod_cast hc1
        rw [mul_assoc, one_div_mul_cancel htpos.ne', mul_one]
        linarith
      · simp [hu]
    calc (∑ u, ∑ v, (if u ∈ H ∧ v ∈ H ∧ G.Adj u v then 1 / (t : ℚ) else 0)) * t
        = ∑ u, (∑ v, (if u ∈ H ∧ v ∈ H ∧ G.Adj u v then 1 / (t : ℚ) else 0)) * t := by
          rw [Finset.sum_mul]
      _ ≤ ∑ u, (if u ∈ H then (H.card : ℚ) - 1 else 0) := Finset.sum_le_sum fun u _ => hper u
      _ = (H.card : ℚ) * (H.card - 1) := by
          rw [Finset.sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  have hS4 : H.card < k →
      ((U.card : ℚ) * U.card - U.card) ≤
        (∑ u, ∑ v, (if H.card < k ∧ G.Adj u v ∧ c u ∈ U ∧ c v ∈ U
          then 1 / (t : ℚ) else 0)) * t := by
    intro hlt
    simp only [hlt, true_and]
    rw [← Finset.sum_product' (f := fun u v => if G.Adj u v ∧ c u ∈ U ∧ c v ∈ U
      then 1 / (t : ℚ) else 0), Finset.sum_ite, sum_const_zero, add_zero, sum_const,
      nsmul_eq_mul, mul_assoc, one_div_mul_cancel htpos.ne', mul_one]
    have hsurj : U.offDiag.card ≤
        ((univ ×ˢ univ).filter fun p : V × V => G.Adj p.1 p.2 ∧ c p.1 ∈ U ∧ c p.2 ∈ U).card := by
      refine Finset.card_le_card_of_surjOn (fun p => (c p.1, c p.2)) ?_
      intro q hq
      rw [mem_coe, mem_offDiag] at hq
      obtain ⟨hq1, hq2, hq3⟩ := hq
      obtain ⟨u, v, huv, hcu, hcv⟩ := hc q.1 q.2 hq3
      refine ⟨(u, v), ?_, ?_⟩
      · rw [mem_coe, mem_filter]
        exact ⟨mem_product.2 ⟨mem_univ _, mem_univ _⟩, huv, hcu ▸ hq1, hcv ▸ hq2⟩
      · simp [hcu, hcv]
    rw [offDiag_card] at hsurj
    have hle : U.card ≤ U.card * U.card := Nat.le_mul_self _
    have : ((U.card * U.card - U.card : ℕ) : ℚ) = (U.card : ℚ) * U.card - U.card := by
      rw [Nat.cast_sub hle, Nat.cast_mul]
    rw [← this]
    exact_mod_cast hsurj
  -- assemble
  have hsum := Finset.sum_le_sum fun u (_ : u ∈ (univ : Finset V)) =>
    Finset.sum_le_sum fun v (_ : v ∈ (univ : Finset V)) =>
      pointwise_bound G c H U ht1 P1 P2 P3' hUout u v
  rw [← two_mul_randicPrime] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [hS1, hS2] at hsum
  set S3 := ∑ u, ∑ v, (if u ∈ H ∧ v ∈ H ∧ G.Adj u v then 1 / (t : ℚ) else 0)
  set S4 := ∑ u, ∑ v, (if H.card < k ∧ G.Adj u v ∧ c u ∈ U ∧ c v ∈ U
    then 1 / (t : ℚ) else 0)
  have hS4nn : 0 ≤ S4 :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => by
      split_ifs
      · positivity
      · exact le_refl 0
  have hmain : (k : ℚ) * t ≤ 2 * randicPrime G * t := by
    have hR : (2 * (H.card : ℚ) - S3 + S4) * t ≤ 2 * randicPrime G * t :=
      mul_le_mul_of_nonneg_right (by linarith) htpos.le
    rcases Nat.lt_or_ge H.card k with hlt | hge
    · have h4 := hS4 hlt
      have hUq : (k : ℚ) - H.card ≤ U.card := by
        have : k - H.card + H.card = k := Nat.sub_add_cancel hHk
        have h' : ((k - H.card : ℕ) : ℚ) ≤ U.card := by exact_mod_cast hUcard
        rw [Nat.cast_sub hHk] at h'
        exact h'
      have hpos : (1 : ℚ) ≤ k - H.card := by
        have : (H.card : ℚ) + 1 ≤ k := by exact_mod_cast hlt
        linarith
      have hsq : ((k : ℚ) - H.card) * ((k : ℚ) - H.card - 1) ≤
          (U.card : ℚ) * U.card - U.card := by
        nlinarith
      have expand : (2 * (H.card : ℚ) - S3 + S4) * t =
          2 * H.card * t - S3 * t + S4 * t := by ring
      rw [expand] at hR
      rw [htq] at hR hS3 h4 ⊢
      nlinarith
    · have hHeq : H.card = k := le_antisymm hHk hge
      have hS4z : S4 = 0 := by
        simp only [S4, hHeq, lt_irrefl, false_and, ite_false, sum_const_zero]
      rw [hS4z] at hR
      have expand : (2 * (H.card : ℚ) - S3 + 0) * t = 2 * H.card * t - S3 * t := by ring
      rw [expand] at hR
      rw [hHeq] at hS3 hR
      rw [htq] at hR hS3 ⊢
      nlinarith
  exact le_of_mul_le_mul_right hmain htpos

omit [Fintype V] [DecidableRel G.Adj] in
/-- A graph with an edge `ab` has a complete 2-pseudocolouring: `a` gets colour `0`,
every other vertex colour `1`. -/
theorem exists_complete_two (a b : V) (hab : G.Adj a b) :
    ∃ c : V → Fin 2, IsCompleteColouring G c := by
  have hne : a ≠ b := G.ne_of_adj hab
  refine ⟨fun x => if x = a then 0 else 1, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact ⟨a, b, hab, by simp, by simp [hne.symm]⟩
  · exact ⟨b, a, hab.symm, by simp [hne.symm], by simp⟩
  · exact absurd rfl hij

/-- **Theorem 1.**  For every finite simple graph with at least one edge and every complete
colouring `c : V → Fin k` (properness not required), `k ≤ 2 R'(G)`. -/
theorem complete_colouring_le_two_randicPrime (hE : G.edgeSet.Nonempty) {k : ℕ}
    (c : V → Fin k) (hc : IsCompleteColouring G c) : (k : ℚ) ≤ 2 * randicPrime G := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨c2, hc2⟩ := exists_complete_two G a b he
      have h2 := two_le_card_bound G (le_refl 2) c2 hc2
      have : (k : ℚ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 hk
      push_cast at h2
      linarith
  · exact two_le_card_bound G hk c hc

end Ach331690
```

## AchMain.lean

```lean
import AchBound
import Mathlib.Data.Fintype.EquivFin

/-!
# Endpoints for MathDB 331690

* `achromatic` and `pseudoachromatic` are genuine maxima (`achromatic_isGreatest`,
  `pseudoachromatic_isGreatest`): every finite graph has a complete proper colouring.
* `achromatic_le_two_randicPrime`, `pseudoachromatic_le_two_randicPrime`: `ψ(G) ≤ 2 R'(G)`
  for every graph with an edge.
* `achromatic_le_two_randicPrime_iff`: on a nonempty vertex set the inequality holds exactly
  when `G` has an edge.
* `achromatic_randic_exact`: on `Fin n`, the inequality holds iff `n = 0` or `G` has an edge.
* `WuElphickConjecture41` (intended form, graphs with an edge) is proved;
  `WuElphickConjecture41Literal` (all graphs) is refuted.
-/

set_option linter.unusedSectionVars false

namespace Ach331690

open Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem le_card_of_hasCompletePseudoColouring {k : ℕ} (h : HasCompletePseudoColouring G k) :
    k ≤ Fintype.card V := by
  obtain ⟨c, hs, -⟩ := h
  simpa using Fintype.card_le_of_surjective c hs

theorem hasCompletePseudoColouring_of_hasCompleteColouring {k : ℕ}
    (h : HasCompleteColouring G k) : HasCompletePseudoColouring G k := by
  obtain ⟨c, hs, -, hc⟩ := h
  exact ⟨c, hs, hc⟩

theorem le_card_of_hasCompleteColouring {k : ℕ} (h : HasCompleteColouring G k) :
    k ≤ Fintype.card V :=
  le_card_of_hasCompletePseudoColouring G (hasCompletePseudoColouring_of_hasCompleteColouring G h)

/-- Every finite graph has a complete proper colouring: a proper colouring with the least
possible number of colours is complete, since two colour classes with no edge between them
could be merged. -/
theorem exists_hasCompleteColouring :
    ∃ k ≤ Fintype.card V, HasCompleteColouring G k := by
  classical
  let Q : ℕ → Prop := fun k => ∃ c : V → Fin k, Function.Surjective c ∧ IsProperColouring G c
  have hQ : Q (Fintype.card V) :=
    ⟨Fintype.equivFin V, (Fintype.equivFin V).surjective,
      fun u v h e => G.ne_of_adj h ((Fintype.equivFin V).injective e)⟩
  have hex : ∃ k, Q k := ⟨_, hQ⟩
  obtain ⟨c, hcs, hcp⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, Nat.find_min' hex hQ, c, hcs, hcp, ?_⟩
  intro i j hij
  by_contra hno
  have hk0pos : 0 < Nat.find hex := Nat.pos_of_ne_zero fun h => by
    have := i.isLt
    omega
  apply Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  let c' : V → Fin (Nat.find hex) := fun v => if c v = j then i else c v
  let s : Finset (Fin (Nat.find hex)) := univ.erase j
  have hs : Fintype.card s = Nat.find hex - 1 := by
    rw [Fintype.card_coe, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  let e : s ≃ Fin (Nat.find hex - 1) := Fintype.equivFinOfCardEq hs
  have hmem : ∀ v, c' v ∈ s := by
    intro v
    simp only [s, c', mem_erase, mem_univ, and_true]
    split_ifs with h
    · exact hij
    · exact h
  refine ⟨fun v => e ⟨c' v, hmem v⟩, ?_, ?_⟩
  · intro y
    have hx : (e.symm y : Fin (Nat.find hex)) ∈ s := (e.symm y).2
    have hxj : (e.symm y : Fin (Nat.find hex)) ≠ j := (mem_erase.1 hx).1
    obtain ⟨v, hv⟩ := hcs (e.symm y)
    refine ⟨v, ?_⟩
    have h2 : (⟨c' v, hmem v⟩ : s) = e.symm y := by
      apply Subtype.ext
      show (if c v = j then i else c v) = _
      rw [hv]
      simp [hxj]
    show e ⟨c' v, hmem v⟩ = y
    rw [h2, e.apply_symm_apply]
  · intro u v huv heq
    have h1 : c' u = c' v := by
      have := congrArg Subtype.val (e.injective heq)
      exact this
    simp only [c'] at h1
    split_ifs at h1 with hu hv hv
    · exact hcp u v huv (hu.trans hv.symm)
    · exact hno ⟨v, u, huv.symm, h1.symm, hu⟩
    · exact hno ⟨u, v, huv, h1, hv⟩
    · exact hcp u v huv h1

theorem hasCompleteColouring_achromatic : HasCompleteColouring G (achromatic G) := by
  classical
  obtain ⟨k, hk, hP⟩ := exists_hasCompleteColouring G
  unfold achromatic
  exact Nat.findGreatest_spec hk hP

theorem le_achromatic {k : ℕ} (h : HasCompleteColouring G k) : k ≤ achromatic G := by
  classical
  unfold achromatic
  exact Nat.le_findGreatest (le_card_of_hasCompleteColouring G h) h

/-- `ψ(G)` is the maximum number of colours in a complete proper colouring of `G`. -/
theorem achromatic_isGreatest :
    IsGreatest {k | HasCompleteColouring G k} (achromatic G) :=
  ⟨hasCompleteColouring_achromatic G, fun _ hk => le_achromatic G hk⟩

theorem hasCompletePseudoColouring_pseudoachromatic :
    HasCompletePseudoColouring G (pseudoachromatic G) := by
  classical
  obtain ⟨k, hk, hP⟩ := exists_hasCompleteColouring G
  unfold pseudoachromatic
  exact Nat.findGreatest_spec hk (hasCompletePseudoColouring_of_hasCompleteColouring G hP)

theorem le_pseudoachromatic {k : ℕ} (h : HasCompletePseudoColouring G k) :
    k ≤ pseudoachromatic G := by
  classical
  unfold pseudoachromatic
  exact Nat.le_findGreatest (le_card_of_hasCompletePseudoColouring G h) h

/-- The pseudoachromatic number is the maximum number of colours in a complete (not
necessarily proper) colouring of `G`. -/
theorem pseudoachromatic_isGreatest :
    IsGreatest {k | HasCompletePseudoColouring G k} (pseudoachromatic G) :=
  ⟨hasCompletePseudoColouring_pseudoachromatic G, fun _ hk => le_pseudoachromatic G hk⟩

theorem achromatic_le_pseudoachromatic : achromatic G ≤ pseudoachromatic G :=
  le_pseudoachromatic G
    (hasCompletePseudoColouring_of_hasCompleteColouring G (hasCompleteColouring_achromatic G))

section Bound

variable [DecidableEq V]

/-- **Theorem (pseudoachromatic form).**  For every finite graph with an edge,
the pseudoachromatic number is at most `2 R'(G)`. -/
theorem pseudoachromatic_le_two_randicPrime (hE : G.edgeSet.Nonempty) :
    (pseudoachromatic G : ℚ) ≤ 2 * randicPrime G := by
  obtain ⟨c, -, hc⟩ := hasCompletePseudoColouring_pseudoachromatic G
  exact complete_colouring_le_two_randicPrime G hE c hc

/-- **Theorem (Wu–Elphick Conjecture 4.1 for graphs with an edge).**
`ψ(G) ≤ 2 R'(G)` for every finite graph with at least one edge. -/
theorem achromatic_le_two_randicPrime (hE : G.edgeSet.Nonempty) :
    (achromatic G : ℚ) ≤ 2 * randicPrime G := by
  obtain ⟨c, -, -, hc⟩ := hasCompleteColouring_achromatic G
  exact complete_colouring_le_two_randicPrime G hE c hc

end Bound

theorem forall_not_adj_of_not_nonempty (hE : ¬ G.edgeSet.Nonempty) : ∀ u v, ¬ G.Adj u v :=
  fun u v h => hE ⟨s(u, v), (SimpleGraph.mem_edgeSet G).2 h⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem edgeSet_nonempty_of_adj {u v : V} (h : G.Adj u v) : G.edgeSet.Nonempty :=
  ⟨s(u, v), (SimpleGraph.mem_edgeSet G).2 h⟩

/-- An edgeless graph on a nonempty vertex set has a complete proper 1-colouring. -/
theorem hasCompleteColouring_one_of_edgeless [Nonempty V] (h : ∀ u v, ¬ G.Adj u v) :
    HasCompleteColouring G 1 := by
  refine ⟨fun _ => 0, ?_, fun u v huv => absurd huv (h u v), ?_⟩
  · intro y
    exact ⟨Classical.arbitrary V, Subsingleton.elim _ _⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij

/-- In an edgeless graph no complete colouring has two or more colours. -/
theorem pseudoachromatic_le_one_of_edgeless (h : ∀ u v, ¬ G.Adj u v) :
    pseudoachromatic G ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c, -, hc⟩ := hasCompletePseudoColouring_pseudoachromatic G
  obtain ⟨u, v, huv, -, -⟩ := hc ⟨0, by omega⟩ ⟨1, hlt⟩ (by simp [Fin.ext_iff])
  exact h u v huv

/-- For a nonempty edgeless graph, `ψ = ψ_s = 1` while `R' = 0`. -/
theorem edgeless_values [Nonempty V] (h : ∀ u v, ¬ G.Adj u v) :
    achromatic G = 1 ∧ pseudoachromatic G = 1 ∧ randicPrime G = 0 := by
  have h1 := le_achromatic G (hasCompleteColouring_one_of_edgeless G h)
  have h2 := achromatic_le_pseudoachromatic G
  have h3 := pseudoachromatic_le_one_of_edgeless G h
  exact ⟨by omega, by omega, randicPrime_eq_zero_of_edgeless G h⟩

/-- On a vertex set with no vertices, `ψ = 0`. -/
theorem achromatic_eq_zero_of_isEmpty [IsEmpty V] : achromatic G = 0 := by
  classical
  unfold achromatic
  rw [Fintype.card_eq_zero]
  exact Nat.findGreatest_zero

section Exact

variable [DecidableEq V]

/-- **Exact truth set on a nonempty vertex set.**  For a graph on a nonempty finite vertex
set, `ψ(G) ≤ 2 R'(G)` holds if and only if `G` has an edge. -/
theorem achromatic_le_two_randicPrime_iff [Nonempty V] :
    (achromatic G : ℚ) ≤ 2 * randicPrime G ↔ G.edgeSet.Nonempty := by
  constructor
  · intro hle
    by_contra hE
    obtain ⟨h1, -, h3⟩ := edgeless_values G (forall_not_adj_of_not_nonempty G hE)
    rw [h1, h3] at hle
    norm_num at hle
  · exact achromatic_le_two_randicPrime G

/-- The same truth set for the pseudoachromatic number. -/
theorem pseudoachromatic_le_two_randicPrime_iff [Nonempty V] :
    (pseudoachromatic G : ℚ) ≤ 2 * randicPrime G ↔ G.edgeSet.Nonempty := by
  constructor
  · intro hle
    by_contra hE
    obtain ⟨-, h2, h3⟩ := edgeless_values G (forall_not_adj_of_not_nonempty G hE)
    rw [h2, h3] at hle
    norm_num at hle
  · exact pseudoachromatic_le_two_randicPrime G

end Exact

/-! ### Statements on `Fin n` -/

/-- **Exact truth set of the literal statement on `Fin n`.**  `ψ(G) ≤ 2 R'(G)` holds if and
only if `n = 0` or `G` has an edge. -/
theorem achromatic_randic_exact (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (achromatic G : ℚ) ≤ 2 * randicPrime G ↔ n = 0 ∨ G.edgeSet.Nonempty := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [true_or, iff_true]
    rw [achromatic_eq_zero_of_isEmpty G]
    have := randicPrime_nonneg G
    push_cast
    linarith
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [achromatic_le_two_randicPrime_iff G]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · omega
      · exact h

/-- **Endpoint (1), colouring form on `Fin n`.**  Every complete colouring
`c : Fin n → Fin k` (properness not required) of a graph with an edge has `k ≤ 2 R'(G)`. -/
theorem fin_complete_colouring_le_two_randicPrime (n k : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (c : Fin n → Fin k) (hE : G.edgeSet.Nonempty)
    (hc : IsCompleteColouring G c) : (k : ℚ) ≤ 2 * randicPrime G :=
  complete_colouring_le_two_randicPrime G hE c hc

/-- **Endpoint (1), achromatic and pseudoachromatic forms on `Fin n`.** -/
theorem fin_achromatic_le_two_randicPrime (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hE : G.edgeSet.Nonempty) :
    (achromatic G : ℚ) ≤ 2 * randicPrime G ∧ (pseudoachromatic G : ℚ) ≤ 2 * randicPrime G :=
  ⟨achromatic_le_two_randicPrime G hE, pseudoachromatic_le_two_randicPrime G hE⟩

/-- **Endpoint (2) on `Fin n`.**  For `n ≥ 1`, `ψ(G) ≤ 2 R'(G)` iff `G` has an edge, and
likewise for the pseudoachromatic number. -/
theorem fin_truth_set (n : ℕ) (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((achromatic G : ℚ) ≤ 2 * randicPrime G ↔ G.edgeSet.Nonempty) ∧
      ((pseudoachromatic G : ℚ) ≤ 2 * randicPrime G ↔ G.edgeSet.Nonempty) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨achromatic_le_two_randicPrime_iff G, pseudoachromatic_le_two_randicPrime_iff G⟩

/-- Wu–Elphick Conjecture 4.1 in the form the source intends: every graph with at least one
edge (the source's proved `R'` results all assume no isolated vertices) satisfies
`ψ(G) ≤ 2 R'(G)`.  Finite graphs are represented on `Fin n`. -/
def WuElphickConjecture41 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.edgeSet.Nonempty → (achromatic G : ℚ) ≤ 2 * randicPrime G

/-- The same conjecture restricted, as in the source's Theorem 1.4, to graphs of order
`n ≥ 1` without isolated vertices. -/
def WuElphickConjecture41NoIsolated : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    0 < n → (∀ v, ∃ w, G.Adj v w) → (achromatic G : ℚ) ≤ 2 * randicPrime G

/-- Wu–Elphick Conjecture 4.1 read literally: "for any graph `G`, `ψ(G) ≤ 2 R'(G)`". -/
def WuElphickConjecture41Literal : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (achromatic G : ℚ) ≤ 2 * randicPrime G

/-- The pseudoachromatic strengthening of the intended conjecture. -/
def PseudoachromaticConjecture : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.edgeSet.Nonempty → (pseudoachromatic G : ℚ) ≤ 2 * randicPrime G

theorem wuElphickConjecture41 : WuElphickConjecture41 :=
  fun _ G _ hE => achromatic_le_two_randicPrime G hE

theorem wuElphickConjecture41NoIsolated : WuElphickConjecture41NoIsolated := by
  intro n G _ hn hiso
  obtain ⟨w, hw⟩ := hiso ⟨0, hn⟩
  exact achromatic_le_two_randicPrime G (edgeSet_nonempty_of_adj G hw)

theorem pseudoachromaticConjecture : PseudoachromaticConjecture :=
  fun _ G _ hE => pseudoachromatic_le_two_randicPrime G hE

/-- The literal unrestricted statement is false: the edgeless graph on one vertex has
`ψ = 1` and `R' = 0`. -/
theorem not_wuElphickConjecture41Literal : ¬ WuElphickConjecture41Literal := by
  intro h
  have := (achromatic_randic_exact 1 (⊥ : SimpleGraph (Fin 1))).1 (h 1 ⊥)
  rcases this with h1 | ⟨e, he⟩
  · omega
  · simp at he

/-- Every counterexample to the literal statement is a nonempty edgeless graph, and every
nonempty edgeless graph is one. -/
theorem literal_counterexamples (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ¬ ((achromatic G : ℚ) ≤ 2 * randicPrime G) ↔ 0 < n ∧ ∀ u v, ¬ G.Adj u v := by
  rw [achromatic_randic_exact]
  constructor
  · intro h
    refine ⟨Nat.pos_of_ne_zero fun h0 => h (Or.inl h0), fun u v huv => h (Or.inr ?_)⟩
    exact edgeSet_nonempty_of_adj G huv
  · rintro ⟨hn, h⟩ (h0 | ⟨e, he⟩)
    · omega
    · induction e using Sym2.ind with
      | _ a b => exact h a b ((SimpleGraph.mem_edgeSet G).1 he)

end Ach331690
```

## AchGrundy.lean

```lean
import AchMain

/-!
# Corollary: Wu–Elphick Conjecture 4.2 (Grundy number) for graphs with an edge

A Grundy `k`-colouring colours each vertex with the smallest colour not used on its
neighbours; equivalently it is proper and every vertex of colour `j` has a neighbour of
each colour `i < j`.  Such a colouring is complete, so `Γ(G) ≤ ψ(G) ≤ 2 R'(G)`.
-/

set_option linter.unusedSectionVars false

namespace Ach331690

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A Grundy colouring: proper, and each vertex has neighbours of all smaller colours. -/
def IsGrundyColouring {k : ℕ} (c : V → Fin k) : Prop :=
  IsProperColouring G c ∧ ∀ v, ∀ i : Fin k, i < c v → ∃ w, G.Adj v w ∧ c w = i

def HasGrundyColouring (k : ℕ) : Prop :=
  ∃ c : V → Fin k, Function.Surjective c ∧ IsGrundyColouring G c

open Classical in
/-- The Grundy number `Γ(G)`: the largest `k` with a Grundy `k`-colouring. -/
noncomputable def grundy : ℕ :=
  Nat.findGreatest (fun k => HasGrundyColouring G k) (Fintype.card V)

theorem isCompleteColouring_of_isGrundy {k : ℕ} (c : V → Fin k) (hs : Function.Surjective c)
    (hg : IsGrundyColouring G c) : IsCompleteColouring G c := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · obtain ⟨v, hv⟩ := hs j
    obtain ⟨w, hw, hcw⟩ := hg.2 v i (hv ▸ h)
    exact ⟨w, v, hw.symm, hcw, hv⟩
  · obtain ⟨v, hv⟩ := hs i
    obtain ⟨w, hw, hcw⟩ := hg.2 v j (hv ▸ h)
    exact ⟨v, w, hw, hv, hcw⟩

theorem hasCompleteColouring_of_hasGrundy {k : ℕ} (h : HasGrundyColouring G k) :
    HasCompleteColouring G k := by
  obtain ⟨c, hs, hg⟩ := h
  exact ⟨c, hs, hg.1, isCompleteColouring_of_isGrundy G c hs hg⟩

/-- `Γ(G) ≤ ψ(G)` (inequality (6) of the source). -/
theorem grundy_le_achromatic : grundy G ≤ achromatic G := by
  classical
  by_cases h0 : grundy G = 0
  · rw [h0]
    exact Nat.zero_le _
  · have hP : HasGrundyColouring G (grundy G) := by
      unfold grundy at h0 ⊢
      exact Nat.findGreatest_of_ne_zero rfl h0
    exact le_achromatic G (hasCompleteColouring_of_hasGrundy G hP)

/-- **Corollary (Wu–Elphick Conjecture 4.2 for graphs with an edge).** -/
theorem grundy_le_two_randicPrime [DecidableEq V] (hE : G.edgeSet.Nonempty) :
    (grundy G : ℚ) ≤ 2 * randicPrime G :=
  le_trans (by exact_mod_cast grundy_le_achromatic G) (achromatic_le_two_randicPrime G hE)

/-- Wu–Elphick Conjecture 4.2, intended form (graphs with an edge). -/
def WuElphickConjecture42 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.edgeSet.Nonempty → (grundy G : ℚ) ≤ 2 * randicPrime G

theorem wuElphickConjecture42 : WuElphickConjecture42 :=
  fun _ G _ hE => grundy_le_two_randicPrime G hE

end Ach331690
```

## AchAxioms.lean

```lean
import AchGrundy

/-!
# Endpoint statements and axiom audit for MathDB 331690
-/

open Ach331690

#print wt
#print randicPrime
#print IsCompleteColouring
#print IsProperColouring
#print HasCompleteColouring
#print HasCompletePseudoColouring
#print achromatic
#print pseudoachromatic
#check @two_mul_randicPrime
#check @complete_colouring_le_two_randicPrime
#check @fin_complete_colouring_le_two_randicPrime
#check @achromatic_isGreatest
#check @pseudoachromatic_isGreatest
#check @achromatic_le_two_randicPrime
#check @pseudoachromatic_le_two_randicPrime
#check @fin_achromatic_le_two_randicPrime
#check @edgeless_values
#check @achromatic_le_two_randicPrime_iff
#check @pseudoachromatic_le_two_randicPrime_iff
#check @fin_truth_set
#check @achromatic_randic_exact
#check @literal_counterexamples
#print WuElphickConjecture41
#print WuElphickConjecture41NoIsolated
#print WuElphickConjecture41Literal
#print PseudoachromaticConjecture
#check @wuElphickConjecture41
#check @wuElphickConjecture41NoIsolated
#check @pseudoachromaticConjecture
#check @not_wuElphickConjecture41Literal

#print IsGrundyColouring
#print grundy
#check @grundy_le_achromatic
#print WuElphickConjecture42
#check @wuElphickConjecture42

#print axioms complete_colouring_le_two_randicPrime
#print axioms fin_complete_colouring_le_two_randicPrime
#print axioms achromatic_isGreatest
#print axioms pseudoachromatic_isGreatest
#print axioms fin_achromatic_le_two_randicPrime
#print axioms fin_truth_set
#print axioms achromatic_randic_exact
#print axioms literal_counterexamples
#print axioms wuElphickConjecture41
#print axioms wuElphickConjecture41NoIsolated
#print axioms pseudoachromaticConjecture
#print axioms not_wuElphickConjecture41Literal
#print axioms grundy_le_achromatic
#print axioms wuElphickConjecture42
```

