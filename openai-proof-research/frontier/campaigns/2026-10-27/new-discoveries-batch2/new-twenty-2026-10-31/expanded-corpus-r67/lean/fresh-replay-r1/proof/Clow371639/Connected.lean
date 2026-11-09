import Clow371639.Refutation

/-!
# Strengthening: the conjecture also fails for connected graphs

`hubGraph k` has the lexicographic power on the left copy, and a hub vertex `inr 0` adjacent to
every other vertex; the remaining right vertices have the hub as their only neighbour.  The graph
is connected, `ω ≤ 2 ^ k + 1`, `χ > ω` for `k ≥ 2`, `χ_f ≥ (5 / 2) ^ k`, and the `5 ^ k - 1`
non-hub right vertices induce an edgeless subgraph.
-/

namespace Clow371639

open Finset

/-- The hub vertex. -/
def hub (k : ℕ) : PadV k := Sum.inr 0

/-- Adjacency of the hub graph. -/
def hubAdj (k : ℕ) (x y : PadV k) : Prop :=
  padAdj k x y ∨ (x ≠ y ∧ (x = hub k ∨ y = hub k))

/-- Lexicographic power of `C₅` plus a dominating hub with `5 ^ k - 1` pendant leaves. -/
def hubGraph (k : ℕ) : SimpleGraph (PadV k) where
  Adj := hubAdj k
  symm := ⟨fun x y h => by
    rcases h with h | ⟨hne, h⟩
    · exact Or.inl ((padGraph k).symm.symm _ _ h)
    · exact Or.inr ⟨hne.symm, h.symm⟩⟩
  loopless := ⟨fun x h => by
    rcases h with h | ⟨hne, -⟩
    · exact (padGraph k).loopless.irrefl x h
    · exact hne rfl⟩

lemma hubGraph_adj_inl_inl (k : ℕ) (u v : Fin k → Fin 5) :
    (hubGraph k).Adj (Sum.inl u) (Sum.inl v) ↔ lexAdj k u v := by
  constructor
  · rintro (h | ⟨-, h | h⟩)
    · exact h
    · exact absurd h (by simp [hub])
    · exact absurd h (by simp [hub])
  · exact Or.inl

lemma hubGraph_adj_inr (k : ℕ) (u : Fin k → Fin 5) (x : PadV k) (hu : Sum.inr u ≠ hub k)
    (h : (hubGraph k).Adj (Sum.inr u) x) : x = hub k := by
  rcases h with h | ⟨-, h | h⟩
  · exact absurd h (padGraph_not_adj_inr k u x)
  · exact absurd h hu
  · exact h

lemma hubGraph_connected (k : ℕ) : (hubGraph k).Connected := by
  have hreach : ∀ x, (hubGraph k).Reachable x (hub k) := by
    intro x
    by_cases hx : x = hub k
    · rw [hx]
    · exact SimpleGraph.Adj.reachable (Or.inr ⟨hx, Or.inr rfl⟩)
  exact SimpleGraph.Connected.mk (fun x y => (hreach x).trans (hreach y).symm)

/-- `ω ≤ 2 ^ k + 1`. -/
lemma hub_cliqueNum_le (k : ℕ) : (hubGraph k).cliqueNum ≤ 2 ^ k + 1 := by
  classical
  refine csSup_le' ?_
  rintro n ⟨s, hs⟩
  rw [← hs.card_eq]
  by_cases hr : ∃ u, Sum.inr u ∈ s ∧ Sum.inr u ≠ hub k
  · obtain ⟨u, hu, hne⟩ := hr
    have : s ⊆ {Sum.inr u, hub k} := by
      intro x hx
      by_cases hxu : x = Sum.inr u
      · simp [hxu]
      · have := hubGraph_adj_inr k u x hne (hs.isClique hu hx (Ne.symm hxu))
        simp [this]
    calc s.card ≤ ({Sum.inr u, hub k} : Finset (PadV k)).card := card_le_card this
      _ ≤ 2 := card_le_two
      _ ≤ 2 ^ k + 1 := by have := Nat.one_le_two_pow (n := k); omega
  · simp only [not_exists, not_and, not_not] at hr
    have hsub : s ⊆ (s.toLeft.map ⟨Sum.inl, Sum.inl_injective⟩) ∪ {hub k} := by
      intro x hx
      rcases x with u | u
      · simp [hx]
      · simp [hr u hx]
    calc s.card ≤ ((s.toLeft.map ⟨Sum.inl, Sum.inl_injective⟩) ∪ {hub k}).card := card_le_card hsub
      _ ≤ (s.toLeft.map ⟨Sum.inl, Sum.inl_injective⟩).card + ({hub k} : Finset (PadV k)).card :=
          card_union_le _ _
      _ = s.toLeft.card + 1 := by simp
      _ ≤ 2 ^ k + 1 := by
          refine Nat.add_le_add_right (lex_clique_card_le k _ ?_) 1
          intro u hu v hv huv
          exact (hubGraph_adj_inl_inl k u v).1
            (hs.isClique (mem_toLeft.1 hu) (mem_toLeft.1 hv) (fun h => huv (Sum.inl_injective h)))

/-- The hub graph is not `(2 ^ k + 1)`-colourable when `k ≥ 2`. -/
lemma hub_not_colorable (k : ℕ) (hk : 2 ≤ k) : ¬ (hubGraph k).Colorable (2 ^ k + 1) := by
  classical
  rintro ⟨C⟩
  have hclass : ∀ c : Fin (2 ^ k + 1),
      (univ.filter (fun u : Fin k → Fin 5 => C (Sum.inl u) = c)).card ≤ 2 ^ k := by
    intro c
    refine lex_indep_card_le k _ ?_
    intro u hu v hv _ hadj
    have h1 := (mem_filter.1 hu).2
    have h2 := (mem_filter.1 hv).2
    exact C.valid ((hubGraph_adj_inl_inl k u v).2 hadj) (h1.trans h2.symm)
  have htot : (univ : Finset (Fin k → Fin 5)).card ≤ (2 ^ k + 1) * 2 ^ k := by
    rw [card_eq_sum_card_fiberwise (f := fun u => C (Sum.inl u)) (t := univ)
      (fun _ _ => mem_coe.2 (mem_univ _))]
    calc ∑ c ∈ (univ : Finset (Fin (2 ^ k + 1))), (univ.filter (fun u : Fin k → Fin 5 =>
            C (Sum.inl u) = c)).card
        ≤ ∑ _c ∈ (univ : Finset (Fin (2 ^ k + 1))), 2 ^ k := sum_le_sum fun c _ => hclass c
      _ = (2 ^ k + 1) * 2 ^ k := by simp
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at htot
  -- `5 ^ k ≥ 4 ^ k + 2 ^ k + 1` for `k ≥ 2`
  have key : ∀ j : ℕ, 4 ^ (j + 2) + 2 ^ (j + 2) < 5 ^ (j + 2) := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      have h4 : 4 ^ (j + 1 + 2) = 4 * 4 ^ (j + 2) := by ring
      have h2 : 2 ^ (j + 1 + 2) = 2 * 2 ^ (j + 2) := by ring
      have h5 : 5 ^ (j + 1 + 2) = 5 * 5 ^ (j + 2) := by ring
      rw [h4, h2, h5]; omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have := key j
  have hmul : (2 ^ (j + 2) + 1) * 2 ^ (j + 2) = 4 ^ (j + 2) + 2 ^ (j + 2) := by
    rw [add_mul, one_mul, ← mul_pow]; norm_num
  omega

/-- `χ > ω` for the hub graph when `k ≥ 2`. -/
lemma hub_cliqueNum_lt_chromaticNumber (k : ℕ) (hk : 2 ≤ k) :
    ((hubGraph k).cliqueNum : ℕ∞) < (hubGraph k).chromaticNumber := by
  have h1 : ((hubGraph k).cliqueNum : ℕ∞) ≤ ((2 ^ k + 1 : ℕ) : ℕ∞) := by
    exact_mod_cast hub_cliqueNum_le k
  have h2 : ((2 ^ k + 1 : ℕ) : ℕ∞) < (hubGraph k).chromaticNumber := by
    rw [lt_iff_not_ge, SimpleGraph.chromaticNumber_le_iff_colorable]
    exact hub_not_colorable k hk
  exact lt_of_le_of_lt h1 h2

/-- Fractional lower bound `χ_f ≥ 5 ^ k / 2 ^ k` for the hub graph. -/
lemma hub_frac_ge (k : ℕ) :
    (5 : ℝ) ^ k / 2 ^ k ≤ fracChromaticNumber (hubGraph k) := by
  classical
  refine le_csInf (fracSet_nonempty _) ?_
  rintro r ⟨y, ⟨hy0, hyind, hycov⟩, rfl⟩
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_le_iff₀ hpos]
  have key : ((5 : ℝ) ^ k) ≤ ∑ I : Finset (PadV k),
      y I * ((univ.filter (fun u : Fin k → Fin 5 => Sum.inl u ∈ I)).card : ℝ) := by
    calc ((5 : ℝ) ^ k) = ∑ _u : Fin k → Fin 5, (1 : ℝ) := by simp
      _ ≤ ∑ u : Fin k → Fin 5, ∑ I ∈ univ.filter (fun I : Finset (PadV k) => Sum.inl u ∈ I),
            y I := sum_le_sum fun u _ => hycov (Sum.inl u)
      _ = ∑ u : Fin k → Fin 5, ∑ I : Finset (PadV k), if Sum.inl u ∈ I then y I else 0 := by
            simp [sum_filter]
      _ = ∑ I : Finset (PadV k), ∑ u : Fin k → Fin 5, if Sum.inl u ∈ I then y I else 0 :=
            sum_comm
      _ = ∑ I : Finset (PadV k),
            y I * ((univ.filter (fun u : Fin k → Fin 5 => Sum.inl u ∈ I)).card : ℝ) := by
            refine sum_congr rfl fun I _ => ?_
            rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  calc (5 : ℝ) ^ k ≤ _ := key
    _ ≤ ∑ I : Finset (PadV k), y I * (2 : ℝ) ^ k := by
        refine sum_le_sum fun I _ => ?_
        by_cases h : y I = 0
        · simp [h]
        · refine mul_le_mul_of_nonneg_left ?_ (hy0 I)
          have hI := hyind I h
          have hb : (univ.filter (fun u : Fin k → Fin 5 => Sum.inl u ∈ I)).card ≤ 2 ^ k := by
            refine lex_indep_card_le k _ ?_
            intro u hu v hv huv hadj
            exact hI (mem_filter.1 hu).2 (mem_filter.1 hv).2 (fun h => huv (Sum.inl_injective h))
              ((hubGraph_adj_inl_inl k u v).2 hadj)
          exact_mod_cast hb
    _ = (∑ I, y I) * 2 ^ k := by rw [sum_mul]

/-- The non-hub right vertices induce an edgeless subgraph, so `|V(H)| ≥ 5 ^ k - 1`. -/
lemma hub_largest_ge (k : ℕ) : 5 ^ k - 1 ≤ largestLowChromaticOrder (hubGraph k) := by
  classical
  let S : Finset (PadV k) := (univ.map ⟨Sum.inr, Sum.inr_injective⟩).erase (hub k)
  have hS : S.card = 5 ^ k - 1 := by
    simp only [S]
    rw [card_erase_of_mem (by simp [hub])]
    simp
  have hbot : (hubGraph k).induce (S : Set (PadV k)) = ⊥ := by
    ext ⟨x, hx⟩ ⟨y, hy⟩
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, SimpleGraph.bot_adj,
      iff_false]
    simp only [S, coe_erase, coe_map, Function.Embedding.coeFn_mk, coe_univ, Set.image_univ,
      Set.mem_sdiff, Set.mem_range, Set.mem_singleton_iff] at hx hy
    obtain ⟨⟨u, rfl⟩, hu⟩ := hx
    intro h
    exact hy.2 (hubGraph_adj_inr k u y hu h)
  have hω : 1 ≤ (hubGraph k).cliqueNum :=
    Nat.one_le_iff_ne_zero.2 (SimpleGraph.cliqueNum_ne_zero_of_finite _)
  have hχ : ((hubGraph k).induce (S : Set (PadV k))).chromaticNumber ≤
      ((hubGraph k).cliqueNum : ℕ∞) := by
    rw [hbot]
    calc (⊥ : SimpleGraph (S : Set (PadV k))).chromaticNumber ≤ ((1 : ℕ) : ℕ∞) :=
          SimpleGraph.Colorable.chromaticNumber_le (SimpleGraph.colorable_one_iff.2 rfl)
      _ ≤ _ := by exact_mod_cast hω
  refine le_csSup ⟨Fintype.card (PadV k), ?_⟩ ⟨S, hS, hχ⟩
  rintro m ⟨s, rfl, -⟩
  exact card_le_univ s

/-- Conjecture 7.5 restricted to connected graphs. -/
def ConnectedConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → (G.cliqueNum : ℕ∞) < G.chromaticNumber →
      fracChromaticNumber G <
        c * ((G.cliqueNum : ℝ) * (Fintype.card V : ℝ) / (largestLowChromaticOrder G : ℝ))

/-- **Strengthening.** Conjecture 7.5 fails even for connected graphs. -/
theorem not_connectedConjecture : ¬ ConnectedConjecture := by
  rintro ⟨c, hc, h⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (8 * c) (by norm_num : (1 : ℝ) < 5 / 4)
  set k := n + 2 with hkdef
  have hk : 2 ≤ k := by omega
  have hkbig : 8 * c ≤ (5 / 4 : ℝ) ^ k := by
    have : (5 / 4 : ℝ) ^ n ≤ (5 / 4) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hlt := h (PadV k) (hubGraph k) (hubGraph_connected k)
    (hub_cliqueNum_lt_chromaticNumber k hk)
  have hfrac := hub_frac_ge k
  have hω : ((hubGraph k).cliqueNum : ℝ) ≤ 2 ^ k + 1 := by exact_mod_cast hub_cliqueNum_le k
  have h5 : (25 : ℝ) ≤ 5 ^ k := by
    calc (25 : ℝ) = 5 ^ 2 := by norm_num
      _ ≤ 5 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have h5n : (25 : ℕ) ≤ 5 ^ k := by exact_mod_cast h5
  have hm : (5 : ℝ) ^ k - 1 ≤ (largestLowChromaticOrder (hubGraph k) : ℝ) := by
    have := hub_largest_ge k
    have h1 : ((5 ^ k - 1 : ℕ) : ℝ) = (5 : ℝ) ^ k - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [← h1]; exact_mod_cast this
  have hcard : (Fintype.card (PadV k) : ℝ) = 2 * 5 ^ k := by
    simp [Fintype.card_sum]; ring
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have h2' : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hden : (0 : ℝ) < 5 ^ k - 1 := by linarith
  have hrhs : c * (((hubGraph k).cliqueNum : ℝ) * (Fintype.card (PadV k) : ℝ) /
      (largestLowChromaticOrder (hubGraph k) : ℝ)) ≤ c * (8 * 2 ^ k) := by
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    rw [hcard, div_le_iff₀ (lt_of_lt_of_le hden hm)]
    calc ((hubGraph k).cliqueNum : ℝ) * (2 * 5 ^ k) ≤ (2 ^ k + 1) * (2 * 5 ^ k) :=
          mul_le_mul_of_nonneg_right hω (by positivity)
      _ ≤ 8 * 2 ^ k * (5 ^ k - 1) := by nlinarith
      _ ≤ 8 * 2 ^ k * (largestLowChromaticOrder (hubGraph k) : ℝ) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
  have hfin : c * (8 * 2 ^ k) ≤ (5 : ℝ) ^ k / 2 ^ k := by
    rw [le_div_iff₀ h2]
    have : (5 : ℝ) ^ k = (5 / 4) ^ k * 2 ^ k * 2 ^ k := by
      rw [mul_assoc, ← mul_pow, ← mul_pow]; norm_num
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_right hkbig (le_of_lt (mul_pos h2 h2))]
  linarith

end Clow371639
