import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/- Copyright 2026 Myeongjin Kang. MIT.
Scoped finite-walk support only. No FPP probability or all-ray classification.
-/
namespace T212M
open scoped BigOperators

noncomputable def changeBudget {E : Type*} (F : Finset E) (w w' : E → ℝ) : ℝ :=
  ∑ e ∈ F, |w' e - w e|

theorem finite_cost_change {E : Type*} [DecidableEq E] (S F : Finset E)
    (w w' : E → ℝ) (hoff : ∀ e, e ∉ F → w' e = w e) :
    |(∑ e ∈ S, w' e) - ∑ e ∈ S, w e| ≤ changeBudget F w w' := by
  calc
    _ = |∑ e ∈ S, (w' e - w e)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ e ∈ S, |w' e - w e| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ e ∈ S ∩ F, |w' e - w e| := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro e he hnot
      have hf : e ∉ F := by simpa [he] using hnot
      simp [hoff e hf]
    _ ≤ changeBudget F w w' := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro e he hnot
      exact abs_nonneg _

noncomputable def walkCost {V : Type*} {G : SimpleGraph V}
    (w : Sym2 V → ℝ) {a b : V} (p : G.Walk a b) : ℝ :=
  (p.edges.map w).sum

theorem walkCost_append {V : Type*} {G : SimpleGraph V}
    (w : Sym2 V → ℝ) {a b c : V} (p : G.Walk a b) (q : G.Walk b c) :
    walkCost w (p.append q) = walkCost w p + walkCost w q := by
  simp [walkCost, SimpleGraph.Walk.edges_append]

theorem walk_cost_change {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (F : Finset (Sym2 V)) (w w' : Sym2 V → ℝ)
    (hoff : ∀ e, e ∉ F → w' e = w e) {a b : V} (p : G.Walk a b)
    (hp : p.edges.Nodup) :
    |walkCost w' p - walkCost w p| ≤ changeBudget F w w' := by
  simpa [walkCost, List.sum_toFinset _ hp] using
    finite_cost_change p.edges.toFinset F w w' hoff

theorem walk_cost_unchanged {V : Type*} {G : SimpleGraph V}
    (F : Finset (Sym2 V)) (w w' : Sym2 V → ℝ)
    (hoff : ∀ e, e ∉ F → w' e = w e) {a b : V} (p : G.Walk a b)
    (havoid : ∀ e ∈ p.edges, e ∉ F) : walkCost w' p = walkCost w p := by
  unfold walkCost
  congr 1
  exact List.map_congr_left fun e he => hoff e (havoid e he)

theorem distance_dominated_by_cost {V : Type*} {G : SimpleGraph V}
    (d : V → V → ℝ) (hzero : ∀ u, d u u = 0)
    (htri : ∀ u v z, d u z ≤ d u v + d v z)
    (w : Sym2 V → ℝ) (hedge : ∀ u v, G.Adj u v → d u v ≤ w s(u, v))
    {a b : V} (p : G.Walk a b) : d a b ≤ walkCost w p := by
  induction p with
  | nil => simp [walkCost, hzero]
  | @cons u v z h q ih =>
    have ht := htri u v z
    have he := hedge u v h
    simp only [walkCost, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons] at *
    linarith

/-- A competitor through a bounded-distance vertex pays a strict detour toll.
The distance axioms and its domination by original walk costs are explicit.
The graph need not be finite and the weights need not have any moment. -/
theorem detour_barrier {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (d : V → V → ℝ) (hsym : ∀ u v, d u v = d v u)
    (htri : ∀ u v z, d u z ≤ d u v + d v z)
    (w w' : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (hoff : ∀ e, e ∉ F → w' e = w e)
    (hdom : ∀ {u v} (p : G.Walk u v), d u v ≤ walkCost w p)
    {x a b c : V} (C : ℝ) (hc : d x c ≤ C)
    (hcal : d x b = d x a + d a b)
    (p : G.Walk a b) (hp : p.edges.Nodup) (hvisit : c ∈ p.support) :
    d a b + 2 * d x a - 2 * C - changeBudget F w w' ≤ walkCost w' p := by
  obtain ⟨q, r, rfl⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hvisit
  have hq := hdom q
  have hr := hdom r
  have hxa := htri x c a
  have hxb := htri x c b
  rw [hsym c a] at hxa
  have hchange := walk_cost_change F w w' hoff (q.append r) hp
  have hloss := (abs_le.mp hchange).1
  simp only [walkCost_append] at hloss ⊢
  linarith

/-- An unchanged calibrated segment beats every edge-simple competitor,
provided each changed edge has an endpoint in the bounded-distance region. -/
theorem late_segment_minimizes {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (d : V → V → ℝ) (hsym : ∀ u v, d u v = d v u)
    (htri : ∀ u v z, d u z ≤ d u v + d v z)
    (w w' : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (hoff : ∀ e, e ∉ F → w' e = w e)
    (hdom : ∀ {u v} (p : G.Walk u v), d u v ≤ walkCost w p)
    {x a b : V} (C : ℝ)
    (hregion : ∀ e ∈ F, ∃ c, c ∈ e ∧ d x c ≤ C)
    (hcal : d x b = d x a + d a b)
    (hlate : C + changeBudget F w w' / 2 < d x a)
    (segment : G.Walk a b) (hsegment : walkCost w segment = d a b)
    (havoid : ∀ e ∈ segment.edges, e ∉ F)
    (p : G.Walk a b) (hp : p.edges.Nodup) :
    walkCost w' segment ≤ walkCost w' p := by
  rw [walk_cost_unchanged F w w' hoff segment havoid, hsegment]
  by_cases hmeet : ∃ e ∈ p.edges, e ∈ F
  · obtain ⟨e, hep, heF⟩ := hmeet
    obtain ⟨c, hce, hc⟩ := hregion e heF
    have hvisit : c ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, hep, hce⟩)
    have hb := detour_barrier d hsym htri w w' F hoff hdom C hc hcal p hp hvisit
    linarith
  · have hno : ∀ e ∈ p.edges, e ∉ F := by simpa only [not_exists, not_and] using hmeet
    rw [walk_cost_unchanged F w w' hoff p hno]
    exact hdom p

theorem walkCost_nonneg {V : Type*} {G : SimpleGraph V} (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) {a b : V} (p : G.Walk a b) : 0 ≤ walkCost w p := by
  induction p with
  | nil => simp [walkCost]
  | @cons u v z h q ih =>
    simp only [walkCost, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons] at *
    exact add_nonneg (hw _) ih

theorem calibrated_segment_avoids {V : Type*} {G : SimpleGraph V}
    (d : V → V → ℝ) (htri : ∀ u v z, d u z ≤ d u v + d v z)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hdom : ∀ {u v} (p : G.Walk u v), d u v ≤ walkCost w p)
    (F : Finset (Sym2 V)) {x a b : V} (C : ℝ)
    (hregion : ∀ e ∈ F, ∃ c, c ∈ e ∧ d x c ≤ C)
    (hcal : d x b = d x a + d a b) (hfar : C < d x a)
    (segment : G.Walk a b) (hsegment : walkCost w segment = d a b) :
    ∀ e ∈ segment.edges, e ∉ F := by
  intro e he heF
  obtain ⟨c, hce, hc⟩ := hregion e heF
  have hvisit : c ∈ segment.support :=
    SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hce⟩)
  obtain ⟨q, r, rfl⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hvisit
  have hq := walkCost_nonneg w hw q
  have hr := hdom r
  have ht := htri x c b
  rw [walkCost_append] at hsegment
  linarith

/-- Deterministic tail stability, against edge-simple competitors. The hypotheses
encode original geodesic segments and escape in original distance. Neither
avoidance of the changed region nor preservation of minimality is assumed. -/
theorem ray_tail_stable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (d : V → V → ℝ) (hsym : ∀ u v, d u v = d v u)
    (htri : ∀ u v z, d u z ≤ d u v + d v z)
    (w w' : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (F : Finset (Sym2 V)) (hoff : ∀ e, e ∉ F → w' e = w e)
    (hdom : ∀ {u v} (p : G.Walk u v), d u v ≤ walkCost w p)
    (x : V) (ray : ℕ → V) (segments : ∀ i j, G.Walk (ray i) (ray j))
    (hsegments : ∀ i j, i ≤ j → walkCost w (segments i j) = d (ray i) (ray j))
    (hcal : ∀ i j, i ≤ j → d x (ray j) = d x (ray i) + d (ray i) (ray j))
    (hescape : ∀ B : ℝ, ∃ N : ℕ, ∀ n, N ≤ n → B < d x (ray n))
    (C : ℝ) (hregion : ∀ e ∈ F, ∃ c, c ∈ e ∧ d x c ≤ C) :
    ∃ N : ℕ, ∀ i, N ≤ i → ∀ j, i ≤ j →
      ∀ p : G.Walk (ray i) (ray j), p.edges.Nodup →
        walkCost w' (segments i j) ≤ walkCost w' p := by
  obtain ⟨N, hN⟩ := hescape (C + changeBudget F w w' / 2)
  have hdelta : 0 ≤ changeBudget F w w' :=
    Finset.sum_nonneg (fun e he => abs_nonneg _)
  refine ⟨N, ?_⟩
  intro i hi j hij p hp
  have hlate := hN i hi
  have hfar : C < d x (ray i) := by linarith
  have havoid := calibrated_segment_avoids d htri w hw hdom F C hregion
    (hcal i j hij) hfar (segments i j) (hsegments i j hij)
  exact late_segment_minimizes d hsym htri w w' F hoff hdom C hregion
    (hcal i j hij) hlate (segments i j) (hsegments i j hij) havoid p hp

end T212M
