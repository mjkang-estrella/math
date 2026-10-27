/-
Copyright (c) 2026 pi implementation sub-agent, pi-sendov-selection-formal lane.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Global continuous selection rigidity (C\*-Sendov infrastructure)

This file is *standalone*: it imports only `Mathlib` and has no dependency on any
other file of the campaign.  It provides the reusable topological infrastructure
for the proposed C\*-algebraic Sendov counterexample described in
`lanes/parent-sendov/PROOF.md`, specifically the **global selection step**:
a pointwise two-valued continuous selection out of two everywhere-distinct
continuous maps on a preconnected space is *globally* equal to one of them, so
pointwise mixing is impossible.

## Main results

* `CStarSendov.continuous_two_point_selection`: general rigidity lemma.  On a
  preconnected space, a continuous map into a pseudo-metric space that takes
  values in two distinct points is globally constant at one of them.
* `CStarSendov.selection_rigidity`: for continuous `b f g : X → ℂ` on a
  preconnected `X` with `f x ≠ g x` for *every* `x`, if `b x = f x ∨ b x = g x`
  for every `x`, then `b = f` or `b = g` as functions.
* `CStarSendov.selection_rigidity_cmap`: the same for bundled continuous maps
  `C(X, ℂ)`.
* `CStarSendov.factor_root_global`: specialization.  Every continuous root `b` of
  the pointwise factor equation `(b - b1) * (b - b2) = 0` is globally `b1` or
  `b2`.  Note the equation is evaluated *pointwise in ℂ before* applying
  `mul_eq_zero`: the function ring `X → ℂ` has zero divisors, so the argument
  must not be run at the level of the function algebra.
* `CStarSendov.no_proximity_factor_root` and
  `CStarSendov.exists_no_proximity_factor_root`: generic proximity obstruction.
  If the two factor roots `b1, b2` are at distance `> 1` from a third map `a0`
  at suitable points `x1, x0`, then *no* continuous factor root `b` satisfies
  the pointwise unit bound `‖b x - a0 x‖ ≤ 1` everywhere.  This discharges the
  load-bearing topological branch of the parent proof (no critical element lies
  in the pointwise C\*-unit disc around the distinguished root).
* `CStarSendov.dist_le_one_iff_normSq_le_one`: bridge between the metric
  unit-distance formulation and the pointwise squared-modulus formulation
  `|b(t) - a0(t)|² ≤ 1` of the C\*-unit disc condition.

## Scope and non-claims

* `Nonempty X` is *not* required anywhere: on an empty space the conclusions are
  vacuous but true, and the proofs go through unchanged.  All that is used is
  `[PreconnectedSpace X]` (for `[0,1]` this holds via the connected instance).
* We do **not** claim the full source endpoint statement, nor any new discovery:
  the explicit `exp`/`sqrt` branch functions, the unit-norm bounds, the scalar
  endpoint values, and the final C\*-algebraic source statement are constructed
  by the parent lane.  This file only supplies the generic selection /
  obstruction layer above.
-/

namespace CStarSendov

open Set Metric

variable {X : Type*} [TopologicalSpace X]

/-! ### Abstract two-point selection rigidity -/

/-- **Two-point selection rigidity.**  If `X` is preconnected and the continuous
map `r : X → Y` into a pseudo-metric space takes values in `{p, q}` at every
point, with `p ≠ q`, then `r` is *globally* constant with value `p` or value `q`.

Proof sketch: separate `p` and `q` by open balls of radius `dist p q / 2`; the
two preimages are open, disjoint, and cover `X`, so preconnectedness forbids
both being nonempty. -/
theorem continuous_two_point_selection [PreconnectedSpace X] {Y : Type*}
    [MetricSpace Y] {r : X → Y} (hr : Continuous r) {p q : Y} (hpq : p ≠ q)
    (hval : ∀ x, r x = p ∨ r x = q) :
    (∀ x, r x = p) ∨ (∀ x, r x = q) := by
  by_contra hcon
  have hp : ¬ ∀ x, r x = p := fun h => hcon (Or.inl h)
  have hq : ¬ ∀ x, r x = q := fun h => hcon (Or.inr h)
  obtain ⟨x0, hx0⟩ := not_forall.mp hp
  obtain ⟨x1, hx1⟩ := not_forall.mp hq
  have hq0 : r x0 = q := (hval x0).resolve_left hx0
  have hp1 : r x1 = p := (hval x1).resolve_right hx1
  have hdpos : 0 < dist p q := dist_pos.mpr hpq
  have hdhalf : 0 < dist p q / 2 := by linarith
  set U : Set X := r ⁻¹' (ball p (dist p q / 2)) with hUdef
  set V : Set X := r ⁻¹' (ball q (dist p q / 2)) with hVdef
  have hUo : IsOpen U := hr.isOpen_preimage _ isOpen_ball
  have hVo : IsOpen V := hr.isOpen_preimage _ isOpen_ball
  have hcov : (Set.univ : Set X) ⊆ U ∪ V := by
    intro x _
    rcases hval x with h | h
    · refine Or.inl (mem_preimage.2 ?_)
      rw [h]
      exact mem_ball_self hdhalf
    · refine Or.inr (mem_preimage.2 ?_)
      rw [h]
      exact mem_ball_self hdhalf
  have hUne : ((Set.univ : Set X) ∩ U).Nonempty :=
    ⟨x1, mem_univ _, mem_preimage.2 (by rw [hp1]; exact mem_ball_self hdhalf)⟩
  have hVne : ((Set.univ : Set X) ∩ V).Nonempty :=
    ⟨x0, mem_univ _, mem_preimage.2 (by rw [hq0]; exact mem_ball_self hdhalf)⟩
  have hdisj : U ∩ V = ∅ := by
    rw [hUdef, hVdef]
    ext x
    refine ⟨fun hc => ?_, fun hc => absurd hc (by simp)⟩
    simp only [mem_inter_iff, mem_preimage] at hc
    obtain ⟨h1, h2⟩ := hc
    have h1' : dist p (r x) < dist p q / 2 := mem_ball'.mp h1
    have h2' : dist q (r x) < dist p q / 2 := mem_ball'.mp h2
    have hlt : dist p q < dist p q := by
      calc dist p q ≤ dist p (r x) + dist (r x) q := dist_triangle _ _ _
        _ < dist p q / 2 + dist p q / 2 := by
              rw [dist_comm (r x) q]
              exact add_lt_add h1' h2'
        _ = dist p q := by ring
    exact absurd hlt (lt_irrefl _)
  have hpreconn := @isPreconnected_univ X _ _
  have hpartition := hpreconn U V hUo hVo hcov hUne hVne
  rw [hdisj] at hpartition
  simp at hpartition

/-! ### Selection rigidity for complex-valued maps -/

/-- **Global selection rigidity.**  Let `X` be preconnected and let
`b f g : X → ℂ` be continuous with `f x ≠ g x` for *every* `x`.  If `b` is a
pointwise selection, i.e. `b x = f x ∨ b x = g x` for every `x`, then `b = f` or
`b = g` globally (as functions).  Pointwise mixing is impossible.

The proof uses the continuous coordinate `r = (b - g) / (f - g)`, which takes
values in `{0, 1}`; by `continuous_two_point_selection` it is globally constant. -/
theorem selection_rigidity [PreconnectedSpace X] {b f g : X → ℂ}
    (hb : Continuous b) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f x ≠ g x) (hsel : ∀ x, b x = f x ∨ b x = g x) :
    b = f ∨ b = g := by
  have hval : ∀ x, (b x - g x) / (f x - g x) = 0 ∨ (b x - g x) / (f x - g x) = 1 := by
    intro x
    rcases hsel x with h | h
    · exact Or.inr (by rw [h, div_self (sub_ne_zero_of_ne (hfg x))])
    · exact Or.inl (by rw [h, sub_self, zero_div])
  have hcont : Continuous fun x => (b x - g x) / (f x - g x) :=
    (hb.sub hg).div (hf.sub hg) fun x => sub_ne_zero_of_ne (hfg x)
  rcases continuous_two_point_selection hcont zero_ne_one hval with h0 | h1
  · -- `r ≡ 0`, hence `b = g`
    refine Or.inr (funext fun x => sub_eq_zero.mp ?_)
    have hx := h0 x
    exact (div_eq_zero_iff.mp hx).resolve_right (sub_ne_zero_of_ne (hfg x))
  · -- `r ≡ 1`, hence `b = f`
    refine Or.inl (funext fun x => ?_)
    have hx := h1 x
    rw [div_eq_one_iff_eq (sub_ne_zero_of_ne (hfg x))] at hx
    -- `hx : b x - g x = f x - g x`
    have hcongr : (b x - g x) + g x = (f x - g x) + g x := by rw [hx]
    simpa using hcongr

/-- Version of `selection_rigidity` for bundled continuous maps `C(X, ℂ)`. -/
theorem selection_rigidity_cmap [PreconnectedSpace X] (b f g : ContinuousMap X ℂ)
    (hfg : ∀ x, f x ≠ g x) (hsel : ∀ x, b x = f x ∨ b x = g x) :
    b = f ∨ b = g := by
  rcases selection_rigidity b.continuous f.continuous g.continuous hfg hsel with h | h
  · exact Or.inl (ContinuousMap.ext fun x => congrFun h x)
  · exact Or.inr (ContinuousMap.ext fun x => congrFun h x)

/-! ### Factor roots of a pointwise quadratic equation -/

/-- **Factor roots are globally selected.**  Let `X` be preconnected and
`b b1 b2 : X → ℂ` continuous with `b1 x ≠ b2 x` for every `x`.  If `b` is a
continuous root of the pointwise factor equation
`(b - b1) * (b - b2) = 0`, then `b = b1` or `b = b2` globally.

*Warning*: the equation is hypothesized *pointwise in ℂ* and `mul_eq_zero` is
applied *after* pointwise evaluation.  The function algebra `X → ℂ` has zero
divisors, so an equation `(b - b1) * (b - b2) = 0` stated at the level of the
algebra would **not** by itself imply the pointwise alternative for arbitrary
elements; here it does because `b` is assumed to satisfy it pointwise (which is
exactly how a root element of the parent's explicit factorization is unpacked). -/
theorem factor_root_global [PreconnectedSpace X] {b b1 b2 : X → ℂ}
    (hb : Continuous b) (hb1 : Continuous b1) (hb2 : Continuous b2)
    (hapart : ∀ x, b1 x ≠ b2 x)
    (hzero : ∀ x, (b x - b1 x) * (b x - b2 x) = 0) :
    b = b1 ∨ b = b2 :=
  selection_rigidity hb hb1 hb2 hapart fun x => by
    rcases (mul_eq_zero).mp (hzero x) with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)

/-! ### Generic proximity obstruction -/

/-- Bridge between the metric condition `dist z w ≤ 1` and the pointwise
squared-modulus condition `Complex.normSq (z - w) ≤ 1` (i.e. `|z - w|² ≤ 1`),
the literal form of membership in the pointwise C\*-unit disc used by the parent. -/
theorem dist_le_one_iff_normSq_le_one {z w : ℂ} :
    dist z w ≤ 1 ↔ Complex.normSq (z - w) ≤ 1 := by
  have key : (‖z - w‖ : ℝ) ^ 2 = Complex.normSq (z - w) := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _)]
  rw [dist_eq_norm]
  constructor
  · intro h
    have h1 : (‖z - w‖ : ℝ) ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (Complex.norm_nonneg (z - w)) (by norm_num)).mpr h
    rwa [key, one_pow] at h1
  · intro h
    have h2 : (‖z - w‖ : ℝ) ^ 2 ≤ (1 : ℝ) ^ 2 := by
      rw [key, one_pow]
      exact h
    exact (sq_le_sq₀ (Complex.norm_nonneg (z - w)) (by norm_num)).mp h2

/-- **Generic proximity obstruction** (function form).  Let `X` be preconnected,
`b1 b2 : X → ℂ` continuous and everywhere apart, and let `a0 : X → ℂ` be a
further map such that at some points `x1, x0` the two factor roots are farther
than `1` from `a0`:

* `1 < ‖a0 x1 - b1 x1‖` and `1 < ‖a0 x0 - b2 x0‖`.

Then *no* continuous factor root `b` of the pointwise equation
`(b - b1) * (b - b2) = 0` can satisfy the pointwise unit bound
`‖b x - a0 x‖ ≤ 1` for every `x`.

This is the reusable form of the parent's final obstruction: if the two global
critical branches exit the unit disc around the distinguished root `a0` at the
endpoint data points, then no continuous selection of critical roots stays in
the pointwise C\*-unit disc around `a0`.  The scalar endpoint values and the
unit-norm bounds are supplied (and verified) by the parent lane. -/
theorem no_proximity_factor_root [PreconnectedSpace X] {a0 b1 b2 : X → ℂ}
    (hb1 : Continuous b1) (hb2 : Continuous b2)
    (hapart : ∀ x, b1 x ≠ b2 x)
    {x0 x1 : X} (h1 : 1 < ‖a0 x1 - b1 x1‖) (h2 : 1 < ‖a0 x0 - b2 x0‖)
    {b : X → ℂ} (hb : Continuous b)
    (hzero : ∀ x, (b x - b1 x) * (b x - b2 x) = 0) :
    ¬ ∀ x, ‖b x - a0 x‖ ≤ 1 := by
  intro hprox
  rcases factor_root_global hb hb1 hb2 hapart hzero with rfl | rfl
  · exact absurd (hprox x1) (not_le.2 (by rw [norm_sub_rev]; exact h1))
  · exact absurd (hprox x0) (not_le.2 (by rw [norm_sub_rev]; exact h2))

/-- **Generic proximity obstruction** (existential form), for discharging the
parent's topological branch directly. -/
theorem exists_no_proximity_factor_root [PreconnectedSpace X] {a0 b1 b2 : X → ℂ}
    (hb1 : Continuous b1) (hb2 : Continuous b2)
    (hapart : ∀ x, b1 x ≠ b2 x)
    {x0 x1 : X} (h1 : 1 < ‖a0 x1 - b1 x1‖) (h2 : 1 < ‖a0 x0 - b2 x0‖) :
    ¬ ∃ b : X → ℂ, Continuous b ∧ (∀ x, (b x - b1 x) * (b x - b2 x) = 0) ∧
      ∀ x, ‖b x - a0 x‖ ≤ 1 := by
  rintro ⟨b, hb, hzero, hprox⟩
  exact no_proximity_factor_root hb1 hb2 hapart h1 h2 hb hzero hprox

/-- **Generic proximity obstruction** (distance form), stating the unit bound as
`dist (b x) (a0 x) ≤ 1`. -/
theorem no_proximity_factor_root_dist [PreconnectedSpace X] {a0 b1 b2 : X → ℂ}
    (hb1 : Continuous b1) (hb2 : Continuous b2)
    (hapart : ∀ x, b1 x ≠ b2 x)
    {x0 x1 : X} (h1 : 1 < dist (a0 x1) (b1 x1)) (h2 : 1 < dist (a0 x0) (b2 x0))
    {b : X → ℂ} (hb : Continuous b)
    (hzero : ∀ x, (b x - b1 x) * (b x - b2 x) = 0) :
    ¬ ∀ x, dist (b x) (a0 x) ≤ 1 := by
  intro hprox
  rcases factor_root_global hb hb1 hb2 hapart hzero with hbeq | hbeq
  · exact absurd (hprox x1) (not_le.2 (by rw [hbeq, dist_comm]; exact h1))
  · exact absurd (hprox x0) (not_le.2 (by rw [hbeq, dist_comm]; exact h2))

end CStarSendov
