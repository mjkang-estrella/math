import Clow371639.Defs
import Clow371639.LexPower
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Refutation of Conjecture 7.5 of arXiv:2511.18747 (MathDB 371639)

`padGraph k` is the disjoint union of the `k`-th lexicographic power of `C₅` (on `5 ^ k` vertices)
with `5 ^ k` isolated vertices.  Then `ω ≤ 2 ^ k`, `χ > 2 ^ k`, `χ_f ≥ (5 / 2) ^ k`, while the
isolated vertices form an induced subgraph with `χ ≤ 1 ≤ ω`, so `|V(H)| ≥ 5 ^ k`.  Hence the
right-hand side of the conjecture is at most `c · 2 ^ (k + 1)`, which is eventually smaller than
`(5 / 2) ^ k`.
-/

namespace Clow371639

open Finset

/-- Vertex type: left copy carries the lexicographic power, right copy is isolated. -/
abbrev PadV (k : ℕ) := (Fin k → Fin 5) ⊕ (Fin k → Fin 5)

/-- Adjacency of the padded graph. -/
def padAdj (k : ℕ) : PadV k → PadV k → Prop
  | Sum.inl u, Sum.inl v => lexAdj k u v
  | _, _ => False

/-- The lexicographic power of `C₅` together with `5 ^ k` isolated vertices. -/
def padGraph (k : ℕ) : SimpleGraph (PadV k) where
  Adj := padAdj k
  symm := ⟨by
    rintro (u | u) (v | v) h <;> simp only [padAdj] at h ⊢
    exact lexAdj_symm k h⟩
  loopless := ⟨by
    rintro (u | u) h <;> simp only [padAdj] at h
    exact lexAdj_irrefl k u h⟩

@[simp] lemma padGraph_adj_inl_inl (k : ℕ) (u v : Fin k → Fin 5) :
    (padGraph k).Adj (Sum.inl u) (Sum.inl v) ↔ lexAdj k u v := Iff.rfl

@[simp] lemma padGraph_not_adj_inr (k : ℕ) (u : Fin k → Fin 5) (x : PadV k) :
    ¬ (padGraph k).Adj (Sum.inr u) x := by
  cases x <;> exact id

@[simp] lemma padGraph_not_adj_inr' (k : ℕ) (u : Fin k → Fin 5) (x : PadV k) :
    ¬ (padGraph k).Adj x (Sum.inr u) := by
  cases x <;> exact id

/-- Left vertices of an independent set of the padded graph number at most `2 ^ k`. -/
lemma pad_indep_left_card_le (k : ℕ) (I : Finset (PadV k))
    (hI : (padGraph k).IsIndepSet (I : Set (PadV k))) :
    (univ.filter (fun u : Fin k → Fin 5 => Sum.inl u ∈ I)).card ≤ 2 ^ k := by
  refine lex_indep_card_le k _ ?_
  intro u hu v hv huv hadj
  have hu' := (mem_filter.1 hu).2
  have hv' := (mem_filter.1 hv).2
  exact hI hu' hv' (fun h => huv (Sum.inl_injective h)) hadj

/-- Clique number bound `ω ≤ 2 ^ k`. -/
lemma pad_cliqueNum_le (k : ℕ) : (padGraph k).cliqueNum ≤ 2 ^ k := by
  classical
  refine csSup_le' ?_
  rintro n ⟨s, hs⟩
  rw [← hs.card_eq]
  by_cases hr : ∃ u, Sum.inr u ∈ s
  · obtain ⟨u, hu⟩ := hr
    have : s ⊆ {Sum.inr u} := by
      intro x hx
      by_contra hne
      exact padGraph_not_adj_inr k u x (hs.isClique hu hx (fun h => hne (by simp [h])))
    calc s.card ≤ ({Sum.inr u} : Finset (PadV k)).card := card_le_card this
      _ = 1 := card_singleton _
      _ ≤ 2 ^ k := Nat.one_le_two_pow
  · simp only [not_exists] at hr
    have hcard : s.card = s.toLeft.card := by
      rw [← card_toLeft_add_card_toRight (u := s)]
      have : s.toRight = ∅ := by
        ext u; simp [hr u]
      simp [this]
    rw [hcard]
    refine lex_clique_card_le k _ ?_
    intro u hu v hv huv
    exact hs.isClique (mem_toLeft.1 hu) (mem_toLeft.1 hv) (fun h => huv (Sum.inl_injective h))

/-- The padded graph is not `2 ^ k`-colourable when `k ≥ 1`. -/
lemma pad_not_colorable (k : ℕ) (hk : 1 ≤ k) : ¬ (padGraph k).Colorable (2 ^ k) := by
  classical
  rintro ⟨C⟩
  have hclass : ∀ c : Fin (2 ^ k),
      (univ.filter (fun u : Fin k → Fin 5 => C (Sum.inl u) = c)).card ≤ 2 ^ k := by
    intro c
    refine lex_indep_card_le k _ ?_
    intro u hu v hv _ hadj
    have h1 := (mem_filter.1 hu).2
    have h2 := (mem_filter.1 hv).2
    exact C.valid (show (padGraph k).Adj (Sum.inl u) (Sum.inl v) from hadj) (h1.trans h2.symm)
  have htot : (univ : Finset (Fin k → Fin 5)).card ≤ 2 ^ k * 2 ^ k := by
    rw [card_eq_sum_card_fiberwise (f := fun u => C (Sum.inl u)) (t := univ)
      (fun _ _ => mem_coe.2 (mem_univ _))]
    calc ∑ c ∈ (univ : Finset (Fin (2 ^ k))), (univ.filter (fun u : Fin k → Fin 5 =>
            C (Sum.inl u) = c)).card
        ≤ ∑ _c ∈ (univ : Finset (Fin (2 ^ k))), 2 ^ k := sum_le_sum fun c _ => hclass c
      _ = 2 ^ k * 2 ^ k := by simp
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← mul_pow] at htot
  have : 4 ^ k < 5 ^ k := Nat.pow_lt_pow_left (by norm_num) (by omega)
  norm_num at htot
  omega

/-- `χ > ω` for the padded graph. -/
lemma pad_cliqueNum_lt_chromaticNumber (k : ℕ) (hk : 1 ≤ k) :
    ((padGraph k).cliqueNum : ℕ∞) < (padGraph k).chromaticNumber := by
  have h1 : ((padGraph k).cliqueNum : ℕ∞) ≤ ((2 ^ k : ℕ) : ℕ∞) := by
    exact_mod_cast pad_cliqueNum_le k
  have h2 : ((2 ^ k : ℕ) : ℕ∞) < (padGraph k).chromaticNumber := by
    rw [lt_iff_not_ge, SimpleGraph.chromaticNumber_le_iff_colorable]
    exact pad_not_colorable k hk
  exact lt_of_le_of_lt h1 h2

/-- The singleton weighting: weight `1` on every one-element set. -/
def singletonWeight {V : Type*} (I : Finset V) : ℝ := if I.card = 1 then 1 else 0

/-- The singleton weighting is a fractional colouring of every graph. -/
lemma isFractionalColoring_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : IsFractionalColoring G singletonWeight := by
  refine ⟨?_, ?_, ?_⟩
  · intro I; unfold singletonWeight; split_ifs <;> norm_num
  · intro I hI
    have h1 : I.card = 1 := by by_contra h; exact hI (by simp [singletonWeight, h])
    obtain ⟨a, rfl⟩ := card_eq_one.1 h1
    intro x hx y hy hxy
    simp only [coe_singleton, Set.mem_singleton_iff] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  · intro v
    have hmem : ({v} : Finset V) ∈ univ.filter (fun I : Finset V => v ∈ I) := by simp
    calc (1 : ℝ) = singletonWeight ({v} : Finset V) := by simp [singletonWeight]
      _ ≤ ∑ I ∈ univ.filter (fun I : Finset V => v ∈ I), singletonWeight I :=
          single_le_sum (f := singletonWeight)
            (fun I _ => by unfold singletonWeight; split_ifs <;> norm_num) hmem

/-- The defining set of `χ_f` is nonempty. -/
lemma fracSet_nonempty {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    {r : ℝ | ∃ y : Finset V → ℝ, IsFractionalColoring G y ∧ ∑ I, y I = r}.Nonempty :=
  ⟨_, singletonWeight, isFractionalColoring_singleton G, rfl⟩

/-- Fractional lower bound `χ_f ≥ 5 ^ k / 2 ^ k`. -/
lemma pad_frac_ge (k : ℕ) :
    (5 : ℝ) ^ k / 2 ^ k ≤ fracChromaticNumber (padGraph k) := by
  classical
  refine le_csInf (fracSet_nonempty _) ?_
  rintro r ⟨y, ⟨hy0, hyind, hycov⟩, rfl⟩
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_le_iff₀ hpos]
  -- double counting over pairs (left vertex, set containing it)
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
          exact_mod_cast pad_indep_left_card_le k I (hyind I h)
    _ = (∑ I, y I) * 2 ^ k := by rw [sum_mul]

/-- The isolated half gives an induced subgraph with `χ ≤ ω`, so `|V(H)| ≥ 5 ^ k`. -/
lemma pad_largest_ge (k : ℕ) : 5 ^ k ≤ largestLowChromaticOrder (padGraph k) := by
  classical
  let S : Finset (PadV k) := univ.map ⟨Sum.inr, Sum.inr_injective⟩
  have hS : S.card = 5 ^ k := by simp [S]
  have hbot : (padGraph k).induce (S : Set (PadV k)) = ⊥ := by
    ext ⟨x, hx⟩ ⟨y, hy⟩
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, SimpleGraph.bot_adj,
      iff_false]
    simp only [S, coe_map, Function.Embedding.coeFn_mk, coe_univ, Set.image_univ,
      Set.mem_range] at hx
    obtain ⟨u, rfl⟩ := hx
    exact padGraph_not_adj_inr k u y
  have hω : 1 ≤ (padGraph k).cliqueNum :=
    Nat.one_le_iff_ne_zero.2 (SimpleGraph.cliqueNum_ne_zero_of_finite _)
  have hχ : ((padGraph k).induce (S : Set (PadV k))).chromaticNumber ≤
      ((padGraph k).cliqueNum : ℕ∞) := by
    rw [hbot]
    calc (⊥ : SimpleGraph (S : Set (PadV k))).chromaticNumber ≤ ((1 : ℕ) : ℕ∞) :=
          SimpleGraph.Colorable.chromaticNumber_le (SimpleGraph.colorable_one_iff.2 rfl)
      _ ≤ _ := by exact_mod_cast hω
  refine le_csSup ⟨Fintype.card (PadV k), ?_⟩ ⟨S, hS, hχ⟩
  rintro m ⟨s, rfl, -⟩
  exact card_le_univ s

/-- **Main theorem.** Conjecture 7.5 of arXiv:2511.18747 (MathDB 371639) is false. -/
theorem not_conjecture : ¬ Conjecture := by
  rintro ⟨c, hc, h⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * c) (by norm_num : (1 : ℝ) < 5 / 4)
  set k := n + 1 with hkdef
  have hk : 1 ≤ k := by omega
  have hkbig : 2 * c ≤ (5 / 4 : ℝ) ^ k := by
    have : (5 / 4 : ℝ) ^ n ≤ (5 / 4) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hlt := h (PadV k) (padGraph k) (pad_cliqueNum_lt_chromaticNumber k hk)
  have hfrac := pad_frac_ge k
  have hω : ((padGraph k).cliqueNum : ℝ) ≤ 2 ^ k := by exact_mod_cast pad_cliqueNum_le k
  have hm : ((5 : ℝ) ^ k) ≤ (largestLowChromaticOrder (padGraph k) : ℝ) := by
    exact_mod_cast pad_largest_ge k
  have hcard : (Fintype.card (PadV k) : ℝ) = 2 * 5 ^ k := by
    simp [Fintype.card_sum]; ring
  have h5 : (0 : ℝ) < 5 ^ k := by positivity
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hrhs : c * (((padGraph k).cliqueNum : ℝ) * (Fintype.card (PadV k) : ℝ) /
      (largestLowChromaticOrder (padGraph k) : ℝ)) ≤ c * (2 ^ k * 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    rw [hcard, div_le_iff₀ (lt_of_lt_of_le h5 hm)]
    have hω0 : (0 : ℝ) ≤ (padGraph k).cliqueNum := Nat.cast_nonneg _
    calc ((padGraph k).cliqueNum : ℝ) * (2 * 5 ^ k) ≤ 2 ^ k * (2 * 5 ^ k) :=
          mul_le_mul_of_nonneg_right hω (by positivity)
      _ = 2 ^ k * 2 * 5 ^ k := by ring
      _ ≤ 2 ^ k * 2 * (largestLowChromaticOrder (padGraph k) : ℝ) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
  have hfin : c * (2 ^ k * 2) ≤ (5 : ℝ) ^ k / 2 ^ k := by
    rw [le_div_iff₀ h2]
    have : (5 : ℝ) ^ k = (5 / 4) ^ k * 2 ^ k * 2 ^ k := by
      rw [mul_assoc, ← mul_pow, ← mul_pow]; norm_num
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_right hkbig (le_of_lt (mul_pos h2 h2))]
  linarith

end Clow371639
