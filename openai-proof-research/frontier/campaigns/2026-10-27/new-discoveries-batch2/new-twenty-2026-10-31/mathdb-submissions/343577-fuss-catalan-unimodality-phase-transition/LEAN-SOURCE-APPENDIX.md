# Lean source appendix — MathDB 343577, stage 2

Status (root, 2026-11-20): the listed endpoint is `FussCatalan.density_measure_phase_transition`, the complete classification for the explicit-density measure, with `mu_supported` and `mu_ne_zero`. The identification of that measure with the moment-defined law, total mass one included, is the source's Proposition 1.1, cited and not proved in Lean. `DensityConjecture` (which adds normalization) is defined below and is not proved; comments in the code that call normalization "still required" refer to that definition. The Lean code below is byte-identical to the author packet's appendix (fuss-catalan-unimodality-343577-formal-paper-sol61-20261120-r2), whose status line read "PARTIAL" relative to the earlier endpoint.

### `FussDefinitions.lean`

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.Set.Function
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Source definitions and the explicit-density measure selected by root for stage 2.
No probability normalization or moment identification of `mu` is asserted here.
The identification with the moment-defined law is a cited published theorem;
the still-open normalization obligation is explicit in `DensityConjecture`.
-/
namespace FussCatalan
open Set Real MeasureTheory

noncomputable def supportRight (p : ℝ) : ℝ := p ^ p * (p-1) ^ (1-p)
noncomputable def rho (p t : ℝ) : ℝ :=
  sin (p*t) ^ p / (sin t * sin ((p-1)*t) ^ (p-1))
noncomputable def angularDensity (p r t : ℝ) : ℝ :=
  sin ((p-1)*t) ^ (p-r-1) * sin t * sin (r*t) /
    (Real.pi * sin (p*t) ^ (p-r))
noncomputable def density (p r x : ℝ) : ℝ :=
  if x ∈ Ioo 0 (supportRight p) then
    angularDensity p r (Function.invFunOn (rho p) (Ioo 0 (Real.pi/p)) x)
  else 0
noncomputable def mu (p r : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (density p r x))

/-- The product formula in the Introduction, including its zeroth-moment convention. -/
noncomputable def raneyMoment (p r : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => r / ((n+1).factorial : ℝ) *
      ∏ i ∈ Finset.range n, (((n+1 : ℕ) : ℝ)*p+r-((i+1 : ℕ) : ℝ))

/-- Compact support in the source interval, probability, integrability and literal moments. -/
def IsRaneyLaw (p r : ℝ) (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ν (Icc 0 (supportRight p))ᶜ = 0 ∧
    ∀ n : ℕ, Integrable (fun x : ℝ => x^n) ν ∧
      (∫ x : ℝ, x^n ∂ν) = raneyMoment p r n

/-- Section 2.2.1: atom at a mode plus a nonnegative density with the two order properties. -/
def Unimodal (ν : Measure ℝ) : Prop :=
  ∃ (b c : ℝ) (f : ℝ → ℝ), 0 ≤ c ∧ (∀ x, 0 ≤ f x) ∧ Measurable f ∧
    MonotoneOn f (Iio b) ∧ AntitoneOn f (Ioi b) ∧
      ν = ENNReal.ofReal c • Measure.dirac b +
        volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- Historical stage-1 target, retained as a definition only; not the selected stage-2 endpoint. -/
def LiteralConjecture : Prop :=
  (∀ p r : ℝ, 1 < p → 0 < r → r ≤ p → IsRaneyLaw p r (mu p r)) ∧
  (∀ p r : ℝ, ∀ ν η : Measure ℝ, IsRaneyLaw p r ν → IsRaneyLaw p r η → ν = η) ∧
  ∀ p : ℝ, 1 < p → ∃ r0 : ℝ, p-1 < r0 ∧ r0 < p ∧
    ∀ r : ℝ, 0 < r → r ≤ p → (Unimodal (mu p r) ↔ r = p ∨ r ≤ r0)

@[simp] theorem raneyMoment_zero (p r : ℝ) : raneyMoment p r 0 = 1 := rfl
@[simp] theorem raneyMoment_one (p r : ℝ) : raneyMoment p r 1 = r := by
  simp [raneyMoment]

/-- A coordinate identity under explicit bijectivity assumptions; it does not prove them. -/
theorem density_coordinate_of_bijOn {p r t : ℝ}
    (h : BijOn (rho p) (Ioo 0 (Real.pi/p)) (Ioo 0 (supportRight p)))
    (ht : t ∈ Ioo 0 (Real.pi/p)) :
    density p r (rho p t) = angularDensity p r t := by
  rw [density, ite_eq_left (h.mapsTo ht), h.injOn.leftInvOn_invFunOn ht]

#print axioms density_coordinate_of_bijOn
end FussCatalan
```

### `FussTrig.lean`

```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Elementary inequalities used in the logarithmic derivative argument. -/
namespace FussCatalan
open Set Real

lemma sin_mul_cos_lt {z : ℝ} (hz : 0 < z) : sin z * cos z < z := by
  have h := Real.sin_lt (show 0 < 2*z by positivity)
  rw [sin_two_mul] at h
  linarith

lemma hasDerivAt_mul_cot {z : ℝ} (hz : sin z ≠ 0) :
    HasDerivAt (fun x : ℝ => x * cot x)
      ((sin z * cos z - z) / sin z ^ 2) z := by
  have h := (hasDerivAt_id z).mul ((hasDerivAt_cos z).div (hasDerivAt_sin z) hz)
  have he : -sin z * sin z - cos z * cos z = -1 := by
    nlinarith [sin_sq_add_cos_sq z]
  rw [he] at h
  convert h using 1
  · ext x
    simp [cot_eq_cos_div_sin]
  · dsimp
    field_simp [hz]
    ring

lemma strictAntiOn_mul_cot :
    StrictAntiOn (fun z : ℝ => z * cot z) (Ioo 0 Real.pi) := by
  have hd : ∀ z ∈ Ioo 0 Real.pi, HasDerivAt (fun x : ℝ => x * cot x)
      ((sin z * cos z - z) / sin z ^ 2) z := by
    intro z hz
    exact hasDerivAt_mul_cot (sin_pos_of_pos_of_lt_pi hz.1 hz.2).ne'
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 Real.pi)
  · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioo] at hz
    rw [(hd z hz).deriv]
    exact div_neg_of_neg_of_pos (sub_neg.mpr (sin_mul_cos_lt hz.1))
      (sq_pos_of_pos (sin_pos_of_pos_of_lt_pi hz.1 hz.2))

lemma scaled_cot_lt {s u t : ℝ} (hs : 0 < s) (hsu : s < u)
    (ht : 0 < t) (hut : u*t < Real.pi) : u*cot (u*t) < s*cot (s*t) := by
  have hst : s*t < u*t := mul_lt_mul_of_pos_right hsu ht
  have h := strictAntiOn_mul_cot
    ⟨mul_pos hs ht, hst.trans hut⟩
    ⟨mul_pos (hs.trans hsu) ht, hut⟩ hst
  have he : t * (u*cot (u*t)) < t * (s*cot (s*t)) := by nlinarith [h]
  exact (mul_lt_mul_iff_right₀ ht).mp he

#print axioms strictAntiOn_mul_cot
#print axioms scaled_cot_lt
end FussCatalan
```

### `FussParameter.lean`

```lean
import FussTrig
import Mathlib.Topology.Order.Monotone

/-! The actual logarithmic-derivative formula and its parameter order structure.
These are analytic helper theorems, not a classification of measures. -/
namespace FussCatalan
open Set Real

noncomputable def D (p r t : ℝ) : ℝ :=
  (p-r-1)*(p-1)*cot ((p-1)*t) + cot t + r*cot (r*t) - (p-r)*p*cot (p*t)

def angleInterval (p : ℝ) : Set ℝ := Ioo 0 (Real.pi/p)

def admissible (p : ℝ) : Set ℝ :=
  {r | 0 < r ∧ r < p ∧ ∀ t ∈ angleInterval p, 0 ≤ D p r t}

lemma scaled_angle_pos_lt_pi {p s t : ℝ} (hp : 0 < p) (hs : 0 < s)
    (hsp : s ≤ p) (ht : t ∈ angleInterval p) : 0 < s*t ∧ s*t < Real.pi := by
  have hpt : p*t < Real.pi := by
    have h := (lt_div_iff₀ hp).mp ht.2
    nlinarith
  exact ⟨mul_pos hs ht.1, (mul_le_mul_of_nonneg_right hsp ht.1.le).trans_lt hpt⟩

lemma sin_scaled_pos {p s t : ℝ} (hp : 0 < p) (hs : 0 < s)
    (hsp : s ≤ p) (ht : t ∈ angleInterval p) : 0 < sin (s*t) := by
  obtain ⟨h0, hπ⟩ := scaled_angle_pos_lt_pi hp hs hsp ht
  exact sin_pos_of_pos_of_lt_pi h0 hπ

lemma D_affine (p r t : ℝ) :
    D p r t = (p-1)^2*cot ((p-1)*t) + cot t - p^2*cot (p*t) +
      r*(p*cot (p*t)-(p-1)*cot ((p-1)*t)) + r*cot (r*t) := by
  unfold D
  ring

/-- The key parameter monotonicity, including comparison with r=p. -/
theorem D_strictAnti_parameter {p t : ℝ} (hp : 1 < p) (ht : t ∈ angleInterval p) :
    StrictAntiOn (fun r => D p r t) (Ioc 0 p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpt := (scaled_angle_pos_lt_pi hp0 hp0 le_rfl ht).2
  have hc : p*cot (p*t) - (p-1)*cot ((p-1)*t) < 0 :=
    sub_neg.mpr (scaled_cot_lt (sub_pos.mpr hp) (by linarith) ht.1 hpt)
  intro r1 hr1 r2 hr2 h12
  have hrt : r2*t < Real.pi := (scaled_angle_pos_lt_pi hp0 hr2.1 hr2.2 ht).2
  have hlast := scaled_cot_lt hr1.1 h12 ht.1 hrt
  have hlin := mul_lt_mul_of_neg_right h12 hc
  change D p r2 t < D p r1 t
  rw [D_affine, D_affine]
  linarith

/-- Actual analytic admissibility is downward closed among positive parameters. -/
theorem admissible_downward {p r1 r2 : ℝ} (hp : 1 < p)
    (h2 : r2 ∈ admissible p) (h1 : 0 < r1) (h12 : r1 ≤ r2) : r1 ∈ admissible p := by
  refine ⟨h1, h12.trans_lt h2.2.1, fun t ht => ?_⟩
  rcases h12.eq_or_lt with h | h
  · simpa only [h] using h2.2.2 t ht
  · exact (h2.2.2 t ht).trans (D_strictAnti_parameter hp ht
      ⟨h1, (h12.trans_lt h2.2.1).le⟩ ⟨h2.1, h2.2.1.le⟩ h).le

lemma continuousAt_parameter_D {p r t : ℝ} (hp : 0 < p) (hr : 0 < r)
    (hrp : r ≤ p) (ht : t ∈ angleInterval p) : ContinuousAt (fun s => D p s t) r := by
  have hs : sin (r*t) ≠ 0 := (sin_scaled_pos hp hr hrp ht).ne'
  unfold D
  simp only [cot_eq_cos_div_sin]
  fun_prop (disch := assumption)

/-- Closure points inside (0,p) retain all the nonnegative derivative inequalities. -/
theorem admissible_closed_inside {p r : ℝ} (hp : 1 < p)
    (hcl : r ∈ closure (admissible p)) (hr : 0 < r) (hrp : r < p) :
    r ∈ admissible p := by
  refine ⟨hr, hrp, fun t ht => ?_⟩
  have hd := continuousAt_parameter_D (lt_trans zero_lt_one hp) hr hrp.le ht
  exact ContinuousWithinAt.closure_le hcl continuousWithinAt_const hd.continuousWithinAt
    (fun s hs => hs.2.2 t ht)

#print axioms D_strictAnti_parameter
#print axioms admissible_downward
#print axioms admissible_closed_inside
end FussCatalan
```

### `FussThreshold.lean`

```lean
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! Supremum assembly with explicit hypotheses; no analytic or measure claims are hidden. -/
namespace FussCatalan
open Set

/-- A relatively closed, downward-closed positive set with a strict interior witness
and a strict upper gap has an included threshold. -/
theorem threshold_of_order_closed {S : Set ℝ} {a p : ℝ}
    (hpos : ∀ r ∈ S, 0 < r)
    (hdown : ∀ r s : ℝ, s ∈ S → 0 < r → r ≤ s → r ∈ S)
    (hclosed : ∀ r ∈ closure S, 0 < r → r < p → r ∈ S)
    (hlower : ∃ q ∈ S, a < q)
    (hupper : ∃ b : ℝ, b < p ∧ ∀ r ∈ S, r ≤ b) :
    ∃ r0 : ℝ, a < r0 ∧ r0 < p ∧ S = Ioc 0 r0 := by
  obtain ⟨q, hq, haq⟩ := hlower
  obtain ⟨b, hbp, hb⟩ := hupper
  have hne : S.Nonempty := ⟨q, hq⟩
  have hbd : BddAbove S := ⟨b, hb⟩
  have hq0 : q ≤ sSup S := le_csSup hbd hq
  have h0p : sSup S < p := (csSup_le hne hb).trans_lt hbp
  have h00 : 0 < sSup S := (hpos q hq).trans_le hq0
  have hmem : sSup S ∈ S := hclosed _ (csSup_mem_closure hne hbd) h00 h0p
  refine ⟨sSup S, haq.trans_le hq0, h0p, ?_⟩
  ext r
  constructor
  · intro hr
    exact ⟨hpos r hr, le_csSup hbd hr⟩
  · intro hr
    exact hdown r (sSup S) hmem hr.1 hr.2

#print axioms threshold_of_order_closed
end FussCatalan
```

### `FussStability.lean`

```lean
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith

/-! The compact positive-slice argument used after extending the angular endpoints. -/
namespace FussCatalan
open Set Filter
open scoped Topology

/-- Pointwise strict positivity is stable in a parameter uniformly over a compact space,
provided joint continuity holds at every point of the slice. -/
theorem compact_slice_positive {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {F : ℝ × K → ℝ} {a : ℝ}
    (hc : ∀ t : K, ContinuousAt F (a,t)) (hpos : ∀ t : K, 0 < F (a,t)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, |r-a| ≤ δ → ∀ t : K, 0 < F (r,t) := by
  have he : ∀ᶠ r in 𝓝 a, ∀ t : K, 0 < F (r,t) := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (P := fun (r : ℝ) (t : K) => 0 < F (r,t)) (x₀ := a)
      (fun t _ => (hc t).eventually (lt_mem_nhds (hpos t)))
    simpa only [mem_univ, forall_const] using h
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε/2, half_pos hε, fun r hr => ?_⟩
  apply he
  have hdist : dist r a ≤ ε/2 := by simpa only [Real.dist_eq] using hr
  exact hdist.trans_lt (half_lt_self hε)

#print axioms compact_slice_positive
end FussCatalan
```

### `FussBaseSlice.lean`

```lean
import FussParameter
import FussThreshold

/-! Positivity on the source's r=p-1 slice and conditional threshold assembly. -/
namespace FussCatalan
open Set Real

lemma cot_add_identity {a t : ℝ} (ht : sin t ≠ 0) (hat : sin (a*t) ≠ 0)
    (hpt : sin ((a+1)*t) ≠ 0) :
    cot t + a*cot (a*t) - (a+1)*cot ((a+1)*t) =
      (sin (a*t)^2 + a*sin t^2) / (sin t*sin (a*t)*sin ((a+1)*t)) := by
  have hs : sin ((a+1)*t) = sin (a*t)*cos t + cos (a*t)*sin t := by
    rw [show (a+1)*t = a*t+t by ring, sin_add]
  have hc : cos ((a+1)*t) = cos (a*t)*cos t - sin (a*t)*sin t := by
    rw [show (a+1)*t = a*t+t by ring, cos_add]
  simp only [cot_eq_cos_div_sin]
  have hpt' : sin (t*(a+1)) ≠ 0 := by simpa only [mul_comm t (a+1)] using hpt
  field_simp [ht, hat, hpt, hpt']
  rw [mul_comm t (a+1), hs, hc]
  have hA := congrArg (fun x : ℝ => sin (a*t)^2*x) (sin_sq_add_cos_sq t)
  have hB := congrArg (fun x : ℝ => a*sin t^2*x) (sin_sq_add_cos_sq (a*t))
  nlinarith only [hA, hB]

/-- Every interior angular point is strictly positive at r=p-1. -/
theorem D_at_p_sub_one_pos {p t : ℝ} (hp : 1 < p) (ht : t ∈ angleInterval p) :
    0 < D p (p-1) t := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have ha : 0 < p-1 := sub_pos.mpr hp
  have h1 : 0 < sin t := by simpa using sin_scaled_pos hp0 zero_lt_one hp.le ht
  have ha1 : 0 < sin ((p-1)*t) := sin_scaled_pos hp0 ha (by linarith) ht
  have hp1 : 0 < sin (p*t) := sin_scaled_pos hp0 hp0 le_rfl ht
  have he : D p (p-1) t =
      cot t + (p-1)*cot ((p-1)*t) - p*cot (p*t) := by unfold D; ring
  rw [he]
  have hi := cot_add_identity h1.ne' ha1.ne'
    (show sin (((p-1)+1)*t) ≠ 0 by simpa using hp1.ne')
  have hi' : cot t + (p-1)*cot ((p-1)*t) - p*cot (p*t) =
      (sin ((p-1)*t)^2 + (p-1)*sin t^2) /
        (sin t*sin ((p-1)*t)*sin (p*t)) := by simpa using hi
  rw [hi']
  exact div_pos (add_pos (sq_pos_of_pos ha1) (mul_pos ha (sq_pos_of_pos h1)))
    (mul_pos (mul_pos h1 ha1) hp1)

/-- Nonemptiness is unconditional; strict extension above p-1 is a separate obligation. -/
theorem p_sub_one_mem_admissible {p : ℝ} (hp : 1 < p) : p-1 ∈ admissible p := by
  exact ⟨sub_pos.mpr hp, by linarith, fun _ ht => (D_at_p_sub_one_pos hp ht).le⟩

/-- All smaller positive parameters satisfy the actual derivative criterion. -/
theorem mem_admissible_of_le_p_sub_one {p r : ℝ} (hp : 1 < p) (hr : 0 < r)
    (hrp : r ≤ p-1) : r ∈ admissible p :=
  admissible_downward hp (p_sub_one_mem_admissible hp) hr hrp

/-- The order part of the phase transition, conditional ONLY on the two remaining
analytic bounds. This is not the literal measure endpoint. -/
theorem derivative_threshold_of_bounds {p : ℝ} (hp : 1 < p)
    (hlower : ∃ q ∈ admissible p, p-1 < q)
    (hupper : ∃ b : ℝ, b < p ∧ ∀ r ∈ admissible p, r ≤ b) :
    ∃ r0 : ℝ, p-1 < r0 ∧ r0 < p ∧ admissible p = Ioc 0 r0 := by
  apply threshold_of_order_closed (fun _ hr => hr.1)
    (fun _ _ hs hr hrs => admissible_downward hp hs hr hrs)
    (fun _ hcl hr hrp => admissible_closed_inside hp hcl hr hrp) hlower hupper

#print axioms D_at_p_sub_one_pos
#print axioms p_sub_one_mem_admissible
#print axioms mem_admissible_of_le_p_sub_one
#print axioms derivative_threshold_of_bounds
end FussCatalan
```

### `FussDensityCalculus.lean`

```lean
import FussDefinitions
import FussParameter
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The formula D really is the logarithmic derivative of the source angular density.
This still does not identify the constructed measure with the moment-defined law. -/
namespace FussCatalan
open Set Real Filter
open scoped Topology

noncomputable def logAngular (p r t : ℝ) : ℝ :=
  (p-r-1)*log (sin ((p-1)*t)) + log (sin t) + log (sin (r*t)) - log Real.pi -
    (p-r)*log (sin (p*t))

lemma angularDensity_pos {p r t : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p)
    (ht : t ∈ angleInterval p) : 0 < angularDensity p r t := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have h1 : 0 < sin t := by simpa using sin_scaled_pos hp0 zero_lt_one hp.le ht
  have ha : 0 < sin ((p-1)*t) := sin_scaled_pos hp0 (sub_pos.mpr hp) (by linarith) ht
  have hpr : 0 < sin (r*t) := sin_scaled_pos hp0 hr hrp ht
  have hpp : 0 < sin (p*t) := sin_scaled_pos hp0 hp0 le_rfl ht
  unfold angularDensity
  exact div_pos (mul_pos (mul_pos (rpow_pos_of_pos ha _) h1) hpr)
    (mul_pos Real.pi_pos (rpow_pos_of_pos hpp _))

lemma log_angularDensity {p r t : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p)
    (ht : t ∈ angleInterval p) : log (angularDensity p r t) = logAngular p r t := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have h1 : 0 < sin t := by simpa using sin_scaled_pos hp0 zero_lt_one hp.le ht
  have ha : 0 < sin ((p-1)*t) := sin_scaled_pos hp0 (sub_pos.mpr hp) (by linarith) ht
  have hpr : 0 < sin (r*t) := sin_scaled_pos hp0 hr hrp ht
  have hpp : 0 < sin (p*t) := sin_scaled_pos hp0 hp0 le_rfl ht
  have hA : 0 < sin ((p-1)*t) ^ (p-r-1) := rpow_pos_of_pos ha _
  have hP : 0 < sin (p*t) ^ (p-r) := rpow_pos_of_pos hpp _
  rw [angularDensity, log_div (mul_pos (mul_pos hA h1) hpr).ne'
    (mul_pos Real.pi_pos hP).ne', log_mul (mul_pos hA h1).ne' hpr.ne',
    log_mul hA.ne' h1.ne', log_mul Real.pi_pos.ne' hP.ne', log_rpow ha, log_rpow hpp]
  unfold logAngular
  ring

lemma hasDerivAt_log_sin_scaled {s t : ℝ} (hs : sin (s*t) ≠ 0) :
    HasDerivAt (fun x : ℝ => log (sin (s*x))) (s*cot (s*t)) t := by
  have h := ((hasDerivAt_sin (s*t)).comp t ((hasDerivAt_id t).const_mul s)).log hs
  convert h using 1
  · rfl
  · simp only [cot_eq_cos_div_sin, Function.comp_apply, mul_one]
    ring

lemma hasDerivAt_logAngular {p r t : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p)
    (ht : t ∈ angleInterval p) : HasDerivAt (logAngular p r) (D p r t) t := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have h1 : sin t ≠ 0 := by simpa using (sin_scaled_pos hp0 zero_lt_one hp.le ht).ne'
  have ha : sin ((p-1)*t) ≠ 0 := (sin_scaled_pos hp0 (sub_pos.mpr hp) (by linarith) ht).ne'
  have hpr : sin (r*t) ≠ 0 := (sin_scaled_pos hp0 hr hrp ht).ne'
  have hpp : sin (p*t) ≠ 0 := (sin_scaled_pos hp0 hp0 le_rfl ht).ne'
  have hOne : HasDerivAt (fun x : ℝ => log (sin x)) (cot t) t := by
    simpa using hasDerivAt_log_sin_scaled (s := 1) (t := t) (by simpa using h1)
  have h := (((((hasDerivAt_log_sin_scaled ha).const_mul (p-r-1)).add hOne).add
    (hasDerivAt_log_sin_scaled hpr)).sub_const (log Real.pi)).sub
    ((hasDerivAt_log_sin_scaled hpp).const_mul (p-r))
  convert h using 1
  · ext x
    simp [logAngular]
  · unfold D
    ring

/-- D is the log derivative of the displayed source density, with all real parameters. -/
theorem hasDerivAt_log_angularDensity {p r t : ℝ} (hp : 1 < p) (hr : 0 < r)
    (hrp : r ≤ p) (ht : t ∈ angleInterval p) :
    HasDerivAt (fun x => log (angularDensity p r x)) (D p r t) t := by
  apply (hasDerivAt_logAngular hp hr hrp ht).congr_of_eventuallyEq
  have hn : angleInterval p ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  filter_upwards [hn] with x hx
  exact log_angularDensity hp hr hrp hx

#print axioms angularDensity_pos
#print axioms hasDerivAt_log_angularDensity
end FussCatalan
```

### `FussDensityMonotonicity.lean`

```lean
import FussDensityCalculus
import FussBaseSlice
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The complete angular-density monotonicity criterion. It is deliberately not
named as a measure-unimodality theorem: the coordinate/measure bridges remain open. -/
namespace FussCatalan
open Set Real

/-- For the actual angular density, monotonicity is exactly the pointwise D criterion. -/
theorem angularDensity_monotone_iff {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p) :
    MonotoneOn (angularDensity p r) (angleInterval p) ↔
      ∀ t ∈ angleInterval p, 0 ≤ D p r t := by
  have hd := fun t ht => hasDerivAt_log_angularDensity hp hr hrp (t := t) ht
  have hg := fun t ht => angularDensity_pos hp hr hrp (t := t) ht
  constructor
  · intro hm t ht
    have hlog : MonotoneOn (fun t => log (angularDensity p r t)) (angleInterval p) := by
      intro x hx y hy hxy
      exact log_le_log (hg x hx) (hm hx hy hxy)
    have hn := hlog.derivWithin_nonneg (x := t)
    rw [derivWithin_of_isOpen (s := angleInterval p) isOpen_Ioo ht, (hd t ht).deriv] at hn
    exact hn
  · intro hnonneg
    have hm : MonotoneOn (fun t => log (angularDensity p r t)) (angleInterval p) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 (Real.pi/p))
      · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ioo] at ht
        exact (hd t ht).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ioo] at ht
        rw [(hd t ht).deriv]
        exact hnonneg t ht
    intro x hx y hy hxy
    exact (log_le_log_iff (hg x hx) (hg y hy)).mp (hm hx hy hxy)

/-- An unconditional result for the displayed formula, not a theorem about mu. -/
theorem angularDensity_monotone_lower_range {p r : ℝ} (hp : 1 < p) (hr : 0 < r)
    (hrp : r ≤ p-1) : MonotoneOn (angularDensity p r) (angleInterval p) := by
  apply (angularDensity_monotone_iff hp hr (by linarith)).mpr
  exact (mem_admissible_of_le_p_sub_one hp hr hrp).2.2

#print axioms angularDensity_monotone_iff
#print axioms angularDensity_monotone_lower_range
end FussCatalan
```

### `FussCoordinate.lean`

```lean
import FussDensityCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Topology.Order.IntermediateValue

namespace FussCatalan
open Set Real Filter
open scoped Topology

lemma supportRight_pos {p : ℝ} (hp : 1 < p) : 0 < supportRight p := by
  exact mul_pos (rpow_pos_of_pos (by linarith) _) (rpow_pos_of_pos (by linarith) _)

lemma angularDensity_continuousOn {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p) :
    ContinuousOn (angularDensity p r) (angleInterval p) := by
  intro t ht
  have h := hasDerivAt_log_angularDensity hp hr hrp ht
  have he : angularDensity p r =ᶠ[𝓝 t] fun x => exp (log (angularDensity p r x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact (exp_log (angularDensity_pos hp hr hrp hx)).symm
  exact (((Real.continuous_exp.continuousAt.comp h.continuousAt)).congr_of_eventuallyEq he).continuousWithinAt

lemma rho_pos {p t : ℝ} (hp : 1 < p) (ht : t ∈ angleInterval p) : 0 < rho p t := by
  have hp0 : 0 < p := by linarith
  have h1 : 0 < sin t := by simpa using sin_scaled_pos hp0 zero_lt_one hp.le ht
  have ha := sin_scaled_pos hp0 (sub_pos.mpr hp) (show p-1 ≤ p by linarith) ht
  have hpt := sin_scaled_pos hp0 hp0 le_rfl ht
  exact div_pos (rpow_pos_of_pos hpt _) (mul_pos h1 (rpow_pos_of_pos ha _))

lemma log_rho {p t : ℝ} (hp : 1 < p) (ht : t ∈ angleInterval p) :
    log (rho p t) = p*log (sin (p*t))-log (sin t)-(p-1)*log (sin ((p-1)*t)) := by
  have hp0 : 0 < p := by linarith
  have h1 : 0 < sin t := by simpa using sin_scaled_pos hp0 zero_lt_one hp.le ht
  have ha := sin_scaled_pos hp0 (sub_pos.mpr hp) (show p-1 ≤ p by linarith) ht
  have hpt := sin_scaled_pos hp0 hp0 le_rfl ht
  rw [rho, log_div (rpow_pos_of_pos hpt _).ne' (mul_pos h1 (rpow_pos_of_pos ha _)).ne',
    log_mul h1.ne' (rpow_pos_of_pos ha _).ne', log_rpow hpt, log_rpow ha]
  ring

lemma hasDerivAt_log_rho {p t : ℝ} (hp : 1 < p) (ht : t ∈ angleInterval p) :
    HasDerivAt (fun t => log (rho p t))
      (p^2*cot (p*t)-cot t-(p-1)^2*cot ((p-1)*t)) t := by
  have hp0 : 0 < p := by linarith
  have h1 : sin t ≠ 0 := by simpa using (sin_scaled_pos hp0 zero_lt_one hp.le ht).ne'
  have ha := (sin_scaled_pos hp0 (sub_pos.mpr hp) (show p-1 ≤ p by linarith) ht).ne'
  have hpt := (sin_scaled_pos hp0 hp0 le_rfl ht).ne'
  have h := (((hasDerivAt_log_sin_scaled hpt).const_mul p).sub
    (hasDerivAt_log_sin_scaled (s := 1) (t := t) (by simpa using h1))).sub
    ((hasDerivAt_log_sin_scaled ha).const_mul (p-1))
  have h' : HasDerivAt (fun x => p*log (sin (p*x))-log (sin x)-
      (p-1)*log (sin ((p-1)*x)))
      (p^2*cot (p*t)-cot t-(p-1)^2*cot ((p-1)*t)) t := by
    convert h using 1
    · ext x; simp only [Pi.sub_apply, one_mul]
    · simp only [one_mul]; ring
  apply h'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
  exact log_rho hp hx

lemma rho_strictAntiOn {p : ℝ} (hp : 1 < p) :
    StrictAntiOn (rho p) (angleInterval p) := by
  have hp0 : 0 < p := by linarith
  have hm : StrictAntiOn (fun t => log (rho p t)) (angleInterval p) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 (Real.pi/p))
    · exact fun t ht => (hasDerivAt_log_rho hp ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      rw [(hasDerivAt_log_rho hp ht).deriv]
      have hpt := (scaled_angle_pos_lt_pi hp0 hp0 le_rfl ht).2
      have hA := scaled_cot_lt (sub_pos.mpr hp) (show p-1 < p by linarith) ht.1 hpt
      have hB := scaled_cot_lt zero_lt_one hp ht.1 hpt
      have h := mul_pos (sub_pos.mpr hp) (sub_pos.mpr hA)
      simp only [one_mul] at hB
      nlinarith
  intro x hx y hy hxy
  exact (log_lt_log_iff (rho_pos hp hy) (rho_pos hp hx)).mp (hm hx hy hxy)

lemma rho_continuousOn {p : ℝ} (hp : 1 < p) :
    ContinuousOn (rho p) (angleInterval p) := by
  intro t ht
  have he : rho p =ᶠ[𝓝 t] fun x => exp (log (rho p x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact (exp_log (rho_pos hp hx)).symm
  exact (((Real.continuous_exp.continuousAt.comp (hasDerivAt_log_rho hp ht).continuousAt)).congr_of_eventuallyEq he).continuousWithinAt

/-- Cancellation of the singular powers at the left angular endpoint. -/
lemma rho_sinc {p t : ℝ} (hp : 1 < p) (ht : t ∈ angleInterval p) :
    rho p t = (p*sinc (p*t))^p /
      (sinc t * ((p-1)*sinc ((p-1)*t))^(p-1)) := by
  have hp0 : 0 < p := by linarith
  have ha : 0 < p-1 := sub_pos.mpr hp
  have hpt := sin_scaled_pos hp0 hp0 le_rfl ht
  have hat := sin_scaled_pos hp0 ha (show p-1 ≤ p by linarith) ht
  rw [sinc_of_ne_zero (mul_pos hp0 ht.1).ne', sinc_of_ne_zero ht.1.ne',
    sinc_of_ne_zero (mul_pos ha ht.1).ne']
  have hP : p*(sin (p*t)/(p*t)) = sin (p*t)/t := by field_simp
  have hA : (p-1)*(sin ((p-1)*t)/((p-1)*t)) = sin ((p-1)*t)/t := by
    field_simp
  rw [hP, hA, div_rpow hpt.le ht.1.le, div_rpow hat.le ht.1.le]
  have htp : t^p = t^(p-1)*t := by
    simpa only [sub_add_cancel] using rpow_add_one ht.1.ne' (p-1)
  rw [htp, rho]
  field_simp [(rpow_pos_of_pos ht.1 (p-1)).ne', ht.1.ne']

lemma rho_limit_left {p : ℝ} (hp : 1 < p) :
    Tendsto (rho p) (𝓝[>] 0) (𝓝 (supportRight p)) := by
  have hp0 : 0 < p := by linarith
  have ha : 0 < p-1 := sub_pos.mpr hp
  have hP : ContinuousAt (fun t : ℝ => (p*sinc (p*t))^p) 0 := by
    apply ContinuousAt.rpow_const
    · fun_prop
    · left; simpa using hp0.ne'
  have hA : ContinuousAt (fun t : ℝ => ((p-1)*sinc ((p-1)*t))^(p-1)) 0 := by
    apply ContinuousAt.rpow_const
    · fun_prop
    · left; simpa using ha.ne'
  have h := hP.div (continuous_sinc.continuousAt.mul hA)
    (show sinc 0 * ((p-1)*sinc ((p-1)*0))^(p-1) ≠ 0 by
      simpa using (rpow_pos_of_pos ha (p-1)).ne')
  change ContinuousAt (fun t : ℝ => (p*sinc (p*t))^p /
      (sinc t * ((p-1)*sinc ((p-1)*t))^(p-1))) 0 at h
  have hv : p^p / (p-1)^(p-1) = supportRight p := by
    rw [supportRight, show 1-p = -(p-1) by ring, rpow_neg ha.le, div_eq_mul_inv]
  have hh : Tendsto (fun t : ℝ => (p*sinc (p*t))^p /
      (sinc t * ((p-1)*sinc ((p-1)*t))^(p-1))) (𝓝[>] 0) (𝓝 (supportRight p)) := by
    simpa only [Pi.div_apply, Pi.mul_apply, mul_zero, sinc_zero, mul_one, one_mul, hv] using h.tendsto.mono_left nhdsWithin_le_nhds
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT (show 0 < Real.pi/p by positivity)] with t ht
  exact (rho_sinc hp ht).symm

lemma rho_limit_right {p : ℝ} (hp : 1 < p) :
    Tendsto (rho p) (𝓝[<] (Real.pi/p)) (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hT : 0 < Real.pi/p := div_pos pi_pos hp0
  have hTπ : Real.pi/p < Real.pi := (div_lt_self pi_pos hp).trans_le le_rfl
  have haT : 0 < (p-1)*(Real.pi/p) := mul_pos (sub_pos.mpr hp) hT
  have haTπ : (p-1)*(Real.pi/p) < Real.pi := by
    have he : p*(Real.pi/p) = Real.pi := mul_div_cancel₀ _ hp0.ne'
    nlinarith
  have hnum : ContinuousAt (fun t : ℝ => sin (p*t)^p) (Real.pi/p) := by
    apply ContinuousAt.rpow_const
    · fun_prop
    · exact Or.inr hp0.le
  have hden : ContinuousAt (fun t : ℝ => sin t * sin ((p-1)*t)^(p-1)) (Real.pi/p) := by
    apply ContinuousAt.mul (by fun_prop)
    apply ContinuousAt.rpow_const (by fun_prop)
    exact Or.inl (sin_pos_of_pos_of_lt_pi haT haTπ).ne'
  have h := hnum.div hden (mul_pos (sin_pos_of_pos_of_lt_pi hT hTπ)
    (rpow_pos_of_pos (sin_pos_of_pos_of_lt_pi haT haTπ) _)).ne'
  change ContinuousAt (rho p) (Real.pi/p) at h
  simpa only [rho, Pi.div_apply, Pi.mul_apply, mul_div_cancel₀ _ hp0.ne', sin_pi, zero_rpow hp0.ne', zero_div] using
    h.tendsto.mono_left nhdsWithin_le_nhds

set_option linter.style.haveILetI false in
lemma rho_bijOn {p : ℝ} (hp : 1 < p) :
    BijOn (rho p) (angleInterval p) (Ioo 0 (supportRight p)) := by
  have hT : 0 < Real.pi/p := div_pos pi_pos (by linarith)
  have hmaps : MapsTo (rho p) (angleInterval p) (Ioo 0 (supportRight p)) := by
    intro t ht
    refine ⟨rho_pos hp ht, ?_⟩
    have hhalf : t/2 ∈ angleInterval p := ⟨half_pos ht.1, (half_lt_self ht.1).trans ht.2⟩
    have hle : rho p (t/2) ≤ supportRight p := by
      apply ge_of_tendsto (rho_limit_left hp)
      filter_upwards [Ioo_mem_nhdsGT (half_pos ht.1)] with s hs
      exact (rho_strictAntiOn hp ⟨hs.1, hs.2.trans hhalf.2⟩ hhalf hs.2).le
    exact (rho_strictAntiOn hp hhalf ht (half_lt_self ht.1)).trans_le hle
  refine ⟨hmaps, (rho_strictAntiOn hp).injOn, ?_⟩
  intro x hx
  exact isPreconnected_Ioo.intermediate_value_Ioo
    (l₁ := 𝓝[<] (Real.pi/p)) (l₂ := 𝓝[>] 0)
    (le_principal_iff.mpr (Ioo_mem_nhdsLT hT))
    (le_principal_iff.mpr (Ioo_mem_nhdsGT hT))
    (rho_continuousOn hp) (rho_limit_right hp) (rho_limit_left hp) hx

lemma density_coordinate {p r t : ℝ} (hp : 1 < p) (ht : t ∈ angleInterval p) :
    density p r (rho p t) = angularDensity p r t :=
  density_coordinate_of_bijOn (rho_bijOn hp) ht

lemma density_nonneg {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p) :
    ∀ x, 0 ≤ density p r x := by
  intro x
  by_cases hx : x ∈ Ioo 0 (supportRight p)
  · obtain ⟨t, ht, rfl⟩ := (rho_bijOn hp).surjOn hx
    rw [density_coordinate hp ht]
    exact (angularDensity_pos hp hr hrp ht).le
  · simp [density, hx]

#print axioms rho_bijOn
#print axioms density_coordinate
#print axioms density_nonneg
#print axioms rho_strictAntiOn
#print axioms rho_limit_left
#print axioms rho_limit_right
end FussCatalan
```

### `FussDensityProperties.lean`

```lean
import FussCoordinate
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace FussCatalan
open Set Real Filter MeasureTheory
open scoped Topology

lemma inverse_rho_strictAntiOn {p : ℝ} (hp : 1 < p) :
    StrictAntiOn (Function.invFunOn (rho p) (angleInterval p)) (Ioo 0 (supportRight p)) := by
  intro x hx y hy hxy
  obtain ⟨s, hs, rfl⟩ := (rho_bijOn hp).surjOn hx
  obtain ⟨t, ht, rfl⟩ := (rho_bijOn hp).surjOn hy
  rw [(rho_bijOn hp).injOn.leftInvOn_invFunOn hs,
    (rho_bijOn hp).injOn.leftInvOn_invFunOn ht]
  by_contra hnot
  have hle := (rho_strictAntiOn hp).antitoneOn hs ht (le_of_not_gt hnot)
  exact hxy.not_ge hle

lemma inverse_rho_continuousOn {p : ℝ} (hp : 1 < p) :
    ContinuousOn (Function.invFunOn (rho p) (angleInterval p)) (Ioo 0 (supportRight p)) := by
  have h := rho_bijOn hp
  have himage : Function.invFunOn (rho p) (angleInterval p) '' Ioo 0 (supportRight p) =
      angleInterval p := by
    rw [← h.image_eq]
    exact h.injOn.invFunOn_image Subset.rfl
  intro x hx
  have ht := h.surjOn.mapsTo_invFunOn hx
  have hc := (inverse_rho_strictAntiOn hp).dual_right.continuousAt_of_image_mem_nhds
    (isOpen_Ioo.mem_nhds hx)
    (show Function.invFunOn (rho p) (angleInterval p) '' Ioo 0 (supportRight p) ∈
      𝓝 (Function.invFunOn (rho p) (angleInterval p) x) by
        rw [himage]; exact isOpen_Ioo.mem_nhds ht)
  exact hc.continuousWithinAt

lemma density_continuousOn {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p) :
    ContinuousOn (density p r) (Ioo 0 (supportRight p)) := by
  have hc := (angularDensity_continuousOn hp hr hrp).comp (inverse_rho_continuousOn hp)
    (rho_bijOn hp).surjOn.mapsTo_invFunOn
  apply hc.congr
  intro x hx
  exact ite_eq_left hx

lemma density_measurable {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p) :
    Measurable (density p r) := by
  have h := (density_continuousOn hp hr hrp).measurable_piecewise
    (g := fun _ => (0:ℝ)) continuousOn_const isOpen_Ioo.measurableSet
  convert h using 1
  ext x
  by_cases hx : x ∈ Ioo 0 (supportRight p)
  · simp [hx]
  · simp [density, hx]

#print axioms density_continuousOn
#print axioms density_measurable
end FussCatalan
```

### `FussUpperGap.lean`

```lean
import FussCoordinate
import FussBaseSlice
import Mathlib.Topology.Algebra.Order.Field

namespace FussCatalan
open Set Real Filter
open scoped Topology

lemma angle_top_factors {p : ℝ} (hp : 1 < p) :
    0 < sin (Real.pi/p) ∧ 0 < sin ((p-1)*(Real.pi/p)) := by
  have hp0 : 0 < p := by linarith
  have hT : 0 < Real.pi/p := div_pos pi_pos hp0
  have hTπ : Real.pi/p < Real.pi := div_lt_self pi_pos hp
  have hA : (p-1)*(Real.pi/p) < Real.pi := by
    have he : p*(Real.pi/p) = Real.pi := mul_div_cancel₀ _ hp0.ne'
    nlinarith
  exact ⟨sin_pos_of_pos_of_lt_pi hT hTπ,
    sin_pos_of_pos_of_lt_pi (mul_pos (sub_pos.mpr hp) hT) hA⟩

lemma cot_at_angle_top {p : ℝ} (hp : 1 < p) :
    Tendsto (fun t => cot (p*t)) (𝓝[<] (Real.pi/p)) atBot := by
  have hp0 : 0 < p := by linarith
  have hs : Tendsto (fun t => sin (p*t)) (𝓝[<] (Real.pi/p)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : ContinuousAt (fun t : ℝ => sin (p*t)) (Real.pi/p) := by fun_prop
      simpa only [mul_div_cancel₀ _ hp0.ne', sin_pi] using h.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (div_pos pi_pos hp0)] with t ht
      exact sin_scaled_pos hp0 hp0 le_rfl ht
  have hc : Tendsto (fun t => cos (p*t)) (𝓝[<] (Real.pi/p)) (𝓝 (-1)) := by
    have h : ContinuousAt (fun t : ℝ => cos (p*t)) (Real.pi/p) := by fun_prop
    simpa only [mul_div_cancel₀ _ hp0.ne', cos_pi] using h.tendsto.mono_left nhdsWithin_le_nhds
  have h := hc.neg_mul_atTop (by norm_num : (-1:ℝ) < 0) hs.inv_tendsto_nhdsGT_zero
  change Tendsto (fun t => cos (p*t) * (sin (p*t))⁻¹) _ _ at h
  simpa only [cot_eq_cos_div_sin, div_eq_mul_inv] using h

lemma D_at_p_tendsto {p : ℝ} (hp : 1 < p) :
    Tendsto (D p p) (𝓝[<] (Real.pi/p)) atBot := by
  have hs := angle_top_factors hp
  have hf : ContinuousAt (fun t : ℝ => -(p-1)*cot ((p-1)*t)+cot t) (Real.pi/p) := by
    simp only [cot_eq_cos_div_sin]
    fun_prop (disch := first | exact hs.1.ne' | exact hs.2.ne')
  have hc := (cot_at_angle_top hp).const_mul_atBot (show 0 < p by linarith)
  have h := hf.tendsto.mono_left nhdsWithin_le_nhds |>.add_atBot hc
  convert h using 1
  ext t
  unfold D
  ring

lemma D_at_p_negative {p : ℝ} (hp : 1 < p) :
    ∃ t ∈ angleInterval p, D p p t < 0 := by
  have he := (D_at_p_tendsto hp).eventually (eventually_lt_atBot (0:ℝ))
  obtain ⟨t, ht, hd⟩ := (he.and (Ioo_mem_nhdsLT (div_pos pi_pos (show 0 < p by linarith)))).exists
  exact ⟨t, hd, ht⟩

lemma admissible_strict_upper {p : ℝ} (hp : 1 < p) :
    ∃ b : ℝ, b < p ∧ ∀ r ∈ admissible p, r ≤ b := by
  obtain ⟨t, ht, hneg⟩ := D_at_p_negative hp
  have hc := continuousAt_parameter_D (show 0 < p by linarith) (show 0 < p by linarith) le_rfl ht
  have he := hc.eventually (gt_mem_nhds hneg)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨p-δ/2, by linarith, fun r hr => ?_⟩
  by_contra hh
  have hlt : p-δ/2 < r := lt_of_not_ge hh
  have hd : dist r p < δ := by rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hr.2.1)]; linarith
  exact (hball hd).not_ge (hr.2.2 t ht)

#print axioms D_at_p_tendsto
#print axioms admissible_strict_upper
end FussCatalan
```

### `FussDensityLimits.lean`

```lean
import FussUpperGap

namespace FussCatalan
open Set Real Filter
open scoped Topology

lemma angularDensity_blowup {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r < p) :
    Tendsto (angularDensity p r) (𝓝[<] (Real.pi/p)) atTop := by
  have hp0 : 0 < p := by linarith
  have hT : 0 < Real.pi/p := div_pos pi_pos hp0
  have hs := angle_top_factors hp
  have hrT : 0 < sin (r*(Real.pi/p)) := by
    apply sin_pos_of_pos_of_lt_pi (mul_pos hr hT)
    have he : p*(Real.pi/p) = Real.pi := mul_div_cancel₀ _ hp0.ne'
    nlinarith
  have hnum : ContinuousAt (fun t : ℝ => sin ((p-1)*t)^(p-r-1)*sin t*sin (r*t))
      (Real.pi/p) := by
    have hA : ContinuousAt (fun t : ℝ => sin ((p-1)*t)^(p-r-1)) (Real.pi/p) := by
      apply ContinuousAt.rpow_const
      · fun_prop
      · exact Or.inl hs.2.ne'
    exact (hA.mul (by fun_prop)).mul (by fun_prop)
  have hden : Tendsto (fun t : ℝ => Real.pi*sin (p*t)^(p-r))
      (𝓝[<] (Real.pi/p)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun t : ℝ => Real.pi*sin (p*t)^(p-r)) (Real.pi/p) := by
        apply continuousAt_const.mul
        apply ContinuousAt.rpow_const (by fun_prop) (Or.inr (sub_pos.mpr hrp).le)
      simpa only [mul_div_cancel₀ _ hp0.ne', sin_pi, zero_rpow (sub_pos.mpr hrp).ne', mul_zero]
        using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT hT] with t ht
      exact mul_pos pi_pos (rpow_pos_of_pos (sin_scaled_pos hp0 hp0 le_rfl ht) _)
  have h := (hnum.tendsto.mono_left nhdsWithin_le_nhds).pos_mul_atTop
    (mul_pos (mul_pos (rpow_pos_of_pos hs.2 _) hs.1) hrT) hden.inv_tendsto_nhdsGT_zero
  change Tendsto (fun t => (sin ((p-1)*t)^(p-r-1)*sin t*sin (r*t))*
    (Real.pi*sin (p*t)^(p-r))⁻¹) _ _ at h
  change Tendsto (fun t => (sin ((p-1)*t)^(p-r-1)*sin t*sin (r*t)) /
    (Real.pi*sin (p*t)^(p-r))) _ _
  simpa only [div_eq_mul_inv] using h

lemma angularDensity_at_p {p t : ℝ} (hp : 1 < p) (ht : t ∈ angleInterval p) :
    angularDensity p p t = sin t*sin (p*t)/(Real.pi*sin ((p-1)*t)) := by
  have hp0 : 0 < p := by linarith
  have hs := sin_scaled_pos hp0 (sub_pos.mpr hp) (show p-1 ≤ p by linarith) ht
  simp only [angularDensity, sub_self, zero_sub, rpow_neg_one, rpow_zero, mul_one]
  field_simp

lemma angularDensity_at_p_limit_right {p : ℝ} (hp : 1 < p) :
    Tendsto (angularDensity p p) (𝓝[<] (Real.pi/p)) (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hs := angle_top_factors hp
  have hc : ContinuousAt (fun t : ℝ => sin t*sin (p*t)/(Real.pi*sin ((p-1)*t)))
      (Real.pi/p) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact (mul_pos pi_pos hs.2).ne'
  have he : Tendsto (fun t : ℝ => sin t*sin (p*t)/(Real.pi*sin ((p-1)*t)))
      (𝓝[<] (Real.pi/p)) (𝓝 0) := by
    simpa only [mul_div_cancel₀ _ hp0.ne', sin_pi, mul_zero, zero_div]
      using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply he.congr'
  filter_upwards [Ioo_mem_nhdsLT (div_pos pi_pos hp0)] with t ht
  exact (angularDensity_at_p hp ht).symm

#print axioms angularDensity_blowup
#print axioms angularDensity_at_p_limit_right
end FussCatalan
```

### `FussCompactification.lean`

```lean
import FussDensityLimits
import FussStability

namespace FussCatalan
open Set Real Filter
open scoped Topology

noncomputable def qcot (z : ℝ) : ℝ := cos z / sinc z

lemma qcot_zero : qcot 0 = 1 := by simp [qcot]

lemma qcot_eq {z : ℝ} (hz : z ≠ 0) : qcot z = z*cot z := by
  by_cases hs : sin z = 0
  · simp [qcot, sinc_of_ne_zero hz, cot_eq_cos_div_sin, hs]
  · unfold qcot
    rw [sinc_of_ne_zero hz, cot_eq_cos_div_sin]
    field_simp

lemma continuousAt_qcot {z : ℝ} (hz : sinc z ≠ 0) : ContinuousAt qcot z :=
  continuous_cos.continuousAt.div continuous_sinc.continuousAt hz

noncomputable def compactD (p r t : ℝ) : ℝ :=
  if t = 0 then Real.pi/p else
  if t = Real.pi/p then (Real.pi/p)*(p-r) else t*(Real.pi/p-t)*D p r t

noncomputable def compactLeft (p r t : ℝ) : ℝ :=
  (Real.pi/p-t)*((p-r-1)*qcot ((p-1)*t)+qcot t+qcot (r*t)-(p-r)*qcot (p*t))

noncomputable def compactRight (p r t : ℝ) : ℝ :=
  t*(Real.pi/p-t)*((p-r-1)*(p-1)*cot ((p-1)*t)+cot t+r*cot (r*t)) +
    (p-r)*t*qcot (p*(Real.pi/p-t))

lemma compactD_eq {p r t : ℝ} (ht : t ∈ angleInterval p) :
    compactD p r t = t*(Real.pi/p-t)*D p r t := by
  simp [compactD, ht.1.ne', ht.2.ne]

lemma compactD_zero (p r : ℝ) : compactD p r 0 = Real.pi/p := by simp [compactD]

lemma compactD_top {p r : ℝ} (hp : 1 < p) :
    compactD p r (Real.pi/p) = (Real.pi/p)*(p-r) := by
  simp [compactD, (div_pos pi_pos (show 0 < p by linarith)).ne']

lemma compactLeft_eq {p r t : ℝ} (hp : 1 < p) (hr : 0 < r)
    (ht : t ∈ Ico 0 (Real.pi/p)) : compactD p r t = compactLeft p r t := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    simp only [compactD_zero, compactLeft, mul_zero, qcot_zero, sub_zero]
    ring
  · rw [compactD_eq ⟨h, ht.2⟩]
    simp only [compactLeft, qcot_eq (mul_pos (sub_pos.mpr hp) h).ne',
      qcot_eq h.ne', qcot_eq (mul_pos hr h).ne',
      qcot_eq (mul_pos (show 0 < p by linarith) h).ne', D]
    ring

lemma compactRight_eq {p r t : ℝ} (hp : 1 < p) (ht : t ∈ Ioc 0 (Real.pi/p)) :
    compactD p r t = compactRight p r t := by
  rcases ht.2.eq_or_lt with h | h
  · subst t
    simp [compactD_top hp, compactRight, qcot_zero, mul_comm]
  · rw [compactD_eq ⟨ht.1, h⟩, compactRight,
      qcot_eq (mul_pos (show 0 < p by linarith) (sub_pos.mpr h)).ne']
    have hc : cot (p*(Real.pi/p-t)) = -cot (p*t) := by
      rw [mul_sub, mul_div_cancel₀ _ (show p ≠ 0 by linarith)]
      simp [cot_eq_cos_div_sin, cos_pi_sub, sin_pi_sub, neg_div]
    rw [hc]
    unfold D
    ring

lemma compactD_continuous_slice {p : ℝ} (hp : 1 < p) :
    ∀ t : Icc (0:ℝ) (Real.pi/p),
      ContinuousAt (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => compactD p z.1 z.2)
        (p-1,t) := by
  intro t
  have hp0 : 0 < p := by linarith
  have hT : 0 < Real.pi/p := div_pos pi_pos hp0
  have ha : 0 < p-1 := sub_pos.mpr hp
  have hcoord : Continuous (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => (z.2:ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  by_cases h0 : (t:ℝ) = 0
  · have hc : ContinuousAt
        (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => compactLeft p z.1 z.2) (p-1,t) := by
      unfold compactLeft
      have hq := continuousAt_qcot (z := 0) (by simp)
      have hqa : ContinuousAt (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => qcot ((p-1)*(z.2:ℝ))) (p-1,t) := by
        apply ContinuousAt.comp' (g := qcot) (x := (p-1,t)) (f := fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => (p-1)*(z.2:ℝ))
        · simpa [h0] using hq
        · fun_prop
      have hq1 : ContinuousAt (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => qcot (z.2:ℝ)) (p-1,t) := by
        apply ContinuousAt.comp' (g := qcot) (x := (p-1,t)) (f := fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => (z.2:ℝ))
        · simpa [h0] using hq
        · exact hcoord.continuousAt
      have hqr : ContinuousAt (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => qcot (z.1*(z.2:ℝ))) (p-1,t) := by
        apply ContinuousAt.comp' (g := qcot) (x := (p-1,t)) (f := fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => z.1*(z.2:ℝ))
        · simpa [h0] using hq
        · fun_prop
      have hqp : ContinuousAt (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => qcot (p*(z.2:ℝ))) (p-1,t) := by
        apply ContinuousAt.comp' (g := qcot) (x := (p-1,t)) (f := fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => p*(z.2:ℝ))
        · simpa [h0] using hq
        · fun_prop
      fun_prop
    apply hc.congr_of_eventuallyEq
    have he1 : ∀ᶠ z : ℝ × Icc (0:ℝ) (Real.pi/p) in 𝓝 (p-1,t), 0 < z.1 :=
      continuous_fst.continuousAt.eventually (lt_mem_nhds ha)
    have he2 : ∀ᶠ z : ℝ × Icc (0:ℝ) (Real.pi/p) in 𝓝 (p-1,t), (z.2:ℝ) < Real.pi/p :=
      hcoord.continuousAt.eventually (gt_mem_nhds (by simpa [h0] using hT))
    filter_upwards [he1, he2] with z hz1 hz2
    exact compactLeft_eq hp hz1 ⟨z.2.property.1,hz2⟩
  · by_cases htop : (t:ℝ) = Real.pi/p
    · have hs := angle_top_factors hp
      have hc : ContinuousAt
          (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => compactRight p z.1 z.2) (p-1,t) := by
        unfold compactRight
        have hqa : ContinuousAt (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => cot ((p-1)*(z.2:ℝ))) (p-1,t) := by
          simp only [cot_eq_cos_div_sin]
          apply ContinuousAt.div (by fun_prop) (by fun_prop)
          simpa only [htop] using hs.2.ne'
        have hq1 : ContinuousAt (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => cot (z.2:ℝ)) (p-1,t) := by
          simp only [cot_eq_cos_div_sin]
          apply ContinuousAt.div (by fun_prop) (by fun_prop)
          simpa only [htop] using hs.1.ne'
        have hqr : ContinuousAt (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => cot (z.1*(z.2:ℝ))) (p-1,t) := by
          simp only [cot_eq_cos_div_sin]
          apply ContinuousAt.div (by fun_prop) (by fun_prop)
          simpa only [htop] using hs.2.ne'
        have hqp : ContinuousAt (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => qcot (p*(Real.pi/p-(z.2:ℝ)))) (p-1,t) := by
          apply ContinuousAt.comp' (g := qcot) (x := (p-1,t)) (f := fun z : ℝ × Icc (0:ℝ) (Real.pi/p) => p*(Real.pi/p-(z.2:ℝ)))
          · simpa [htop] using continuousAt_qcot (z := 0) (by simp)
          · fun_prop
        fun_prop
      apply hc.congr_of_eventuallyEq
      have he : ∀ᶠ z : ℝ × Icc (0:ℝ) (Real.pi/p) in 𝓝 (p-1,t), 0 < (z.2:ℝ) :=
        hcoord.continuousAt.eventually (lt_mem_nhds (by simpa [htop] using hT))
      filter_upwards [he] with z hz
      exact compactRight_eq hp ⟨hz, z.2.property.2⟩
    · have ht : (t:ℝ) ∈ angleInterval p :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm h0), lt_of_le_of_ne t.property.2 htop⟩
      have h1 : sin (t:ℝ) ≠ 0 := by simpa using (sin_scaled_pos hp0 zero_lt_one hp.le ht).ne'
      have hA := (sin_scaled_pos hp0 ha (show p-1 ≤ p by linarith) ht).ne'
      have hP := (sin_scaled_pos hp0 hp0 le_rfl ht).ne'
      have hc : ContinuousAt (fun z : ℝ × Icc (0:ℝ) (Real.pi/p) =>
          (z.2:ℝ)*(Real.pi/p-(z.2:ℝ))*D p z.1 z.2) (p-1,t) := by
        unfold D
        simp only [cot_eq_cos_div_sin]
        fun_prop (disch := first | exact h1 | exact hA | exact hP)
      apply hc.congr_of_eventuallyEq
      have he : ∀ᶠ z : ℝ × Icc (0:ℝ) (Real.pi/p) in 𝓝 (p-1,t),
          (z.2:ℝ) ∈ angleInterval p := hcoord.continuousAt.eventually (isOpen_Ioo.mem_nhds ht)
      filter_upwards [he] with z hz
      exact compactD_eq hz

lemma admissible_strict_lower {p : ℝ} (hp : 1 < p) :
    ∃ q ∈ admissible p, p-1 < q := by
  have hT : 0 < Real.pi/p := div_pos pi_pos (by linarith)
  have hpos : ∀ t : Icc (0:ℝ) (Real.pi/p), 0 < compactD p (p-1) t := by
    intro t
    by_cases h0 : (t:ℝ) = 0
    · simpa only [h0, compactD_zero] using hT
    · by_cases htop : (t:ℝ) = Real.pi/p
      · simpa only [htop, compactD_top hp, sub_sub_cancel, mul_one] using hT
      · have ht : (t:ℝ) ∈ angleInterval p :=
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm h0), lt_of_le_of_ne t.property.2 htop⟩
        rw [compactD_eq ht]
        exact mul_pos (mul_pos ht.1 (sub_pos.mpr ht.2)) (D_at_p_sub_one_pos hp ht)
  obtain ⟨δ, hδ, hδpos⟩ := compact_slice_positive (compactD_continuous_slice hp) hpos
  let ε := min δ 1 / 2
  have hε : 0 < ε := half_pos (lt_min hδ zero_lt_one)
  have hεδ : ε ≤ δ := (half_le_self (le_of_lt (lt_min hδ zero_lt_one))).trans (min_le_left _ _)
  have hε1 : ε < 1 := (half_lt_self (lt_min hδ zero_lt_one)).trans_le (min_le_right _ _)
  let q := p-1+ε
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hqp : q < p := by dsimp [q]; linarith
  refine ⟨q, ⟨hq0, hqp, fun t ht => ?_⟩, by dsimp [q]; linarith⟩
  have hqdist : |q-(p-1)| ≤ δ := by
    simpa only [q, add_sub_cancel_left, abs_of_pos hε] using hεδ
  have hF := hδpos q hqdist (⟨t, ht.1.le, ht.2.le⟩ : Icc (0:ℝ) (Real.pi/p))
  rw [compactD_eq ht] at hF
  exact (pos_of_mul_pos_right hF (mul_pos ht.1 (sub_pos.mpr ht.2)).le).le

/-- The strict threshold for the actual logarithmic derivative, unconditionally. -/
theorem derivative_threshold {p : ℝ} (hp : 1 < p) :
    ∃ r0 : ℝ, p-1 < r0 ∧ r0 < p ∧ admissible p = Ioc 0 r0 :=
  derivative_threshold_of_bounds hp (admissible_strict_lower hp) (admissible_strict_upper hp)

#print axioms admissible_strict_lower
#print axioms derivative_threshold
#print axioms compactD_continuous_slice
end FussCatalan
```

### `FussExceptional.lean`

```lean
import FussDensityLimits
import FussDensityMonotonicity
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace FussCatalan
open Set Real Filter
open scoped Topology

noncomputable def sineRatio (p t : ℝ) : ℝ := sin (p*t)/sin t

lemma sineRatio_pos {p t : ℝ} (hp : 1 < p) (ht : t ∈ angleInterval p) :
    0 < sineRatio p t := by
  have hp0 : 0 < p := by linarith
  exact div_pos (sin_scaled_pos hp0 hp0 le_rfl ht)
    (by simpa using sin_scaled_pos hp0 zero_lt_one hp.le ht)

lemma hasDerivAt_log_sineRatio {p t : ℝ} (hp : 1 < p) (ht : t ∈ angleInterval p) :
    HasDerivAt (fun t => log (sineRatio p t)) (p*cot (p*t)-cot t) t := by
  have hp0 : 0 < p := by linarith
  have h1 : sin t ≠ 0 := by simpa using (sin_scaled_pos hp0 zero_lt_one hp.le ht).ne'
  have hP := (sin_scaled_pos hp0 hp0 le_rfl ht).ne'
  have h := (hasDerivAt_log_sin_scaled hP).sub
    (hasDerivAt_log_sin_scaled (s := 1) (t := t) (by simpa using h1))
  simp only [one_mul] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
  exact log_div (sin_scaled_pos hp0 hp0 le_rfl hx).ne'
    (show sin x ≠ 0 by simpa using (sin_scaled_pos hp0 zero_lt_one hp.le hx).ne')

lemma ratio_strictAntiOn {p : ℝ} (hp : 1 < p) :
    StrictAntiOn (sineRatio p) (angleInterval p) := by
  have hp0 : 0 < p := by linarith
  have hm : StrictAntiOn (fun t => log (sineRatio p t)) (angleInterval p) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 (Real.pi/p))
    · exact fun t ht => (hasDerivAt_log_sineRatio hp ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      rw [(hasDerivAt_log_sineRatio hp ht).deriv]
      have h := scaled_cot_lt zero_lt_one hp ht.1
        (scaled_angle_pos_lt_pi hp0 hp0 le_rfl ht).2
      simpa only [one_mul, sub_neg] using h
  intro x hx y hy hxy
  exact (log_lt_log_iff (sineRatio_pos hp hy) (sineRatio_pos hp hx)).mp (hm hx hy hxy)

lemma sineRatio_continuousOn {p : ℝ} (hp : 1 < p) :
    ContinuousOn (sineRatio p) (angleInterval p) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  unfold sineRatio
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simpa using (sin_scaled_pos (show 0 < p by linarith) zero_lt_one hp.le ht).ne'

lemma sineRatio_limit_left {p : ℝ} (hp : 1 < p) :
    Tendsto (sineRatio p) (𝓝[>] 0) (𝓝 p) := by
  have hc : ContinuousAt (fun t : ℝ => p*sinc (p*t)/sinc t) 0 := by
    apply ContinuousAt.div (by fun_prop) continuous_sinc.continuousAt (by simp)
  have hh : Tendsto (fun t : ℝ => p*sinc (p*t)/sinc t) (𝓝[>] 0) (𝓝 p) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  rw [sinc_of_ne_zero (mul_pos (show 0 < p by linarith) ht).ne', sinc_of_ne_zero ht.ne']
  unfold sineRatio
  field_simp [ht0.ne']

lemma sineRatio_limit_right {p : ℝ} (hp : 1 < p) :
    Tendsto (sineRatio p) (𝓝[<] (Real.pi/p)) (𝓝 0) := by
  have hc : ContinuousAt (sineRatio p) (Real.pi/p) := by
    unfold sineRatio
    apply ContinuousAt.div (by fun_prop) (by fun_prop) (angle_top_factors hp).1.ne'
  simpa only [sineRatio, mul_div_cancel₀ _ (show p ≠ 0 by linarith), sin_pi, zero_div]
    using hc.tendsto.mono_left nhdsWithin_le_nhds

lemma ratio_crossing {p : ℝ} (hp : 1 < p) : ∃ t0 ∈ angleInterval p,
    sineRatio p t0 = sqrt p := by
  have hp0 : 0 < p := by linarith
  have hT : 0 < Real.pi/p := div_pos pi_pos hp0
  have hs : 0 < sqrt p := sqrt_pos.mpr hp0
  have hsp : sqrt p < p := by nlinarith [sq_sqrt hp0.le]
  exact isPreconnected_Ioo.intermediate_value_Ioo
    (l₁ := 𝓝[<] (Real.pi/p)) (l₂ := 𝓝[>] 0)
    (le_principal_iff.mpr (Ioo_mem_nhdsLT hT))
    (le_principal_iff.mpr (Ioo_mem_nhdsGT hT))
    (sineRatio_continuousOn hp) (sineRatio_limit_right hp) (sineRatio_limit_left hp) ⟨hs,hsp⟩

lemma hasDerivAt_angularDensity_at_p {p t : ℝ} (hp : 1 < p) (ht : t ∈ angleInterval p) :
    HasDerivAt (angularDensity p p)
      ((sin (p*t)^2-p*sin t^2)/(Real.pi*sin ((p-1)*t)^2)) t := by
  have hp0 : 0 < p := by linarith
  have hA := (sin_scaled_pos hp0 (sub_pos.mpr hp) (show p-1 ≤ p by linarith) ht).ne'
  have h := ((hasDerivAt_sin t).mul
    ((hasDerivAt_sin (p*t)).comp t ((hasDerivAt_id t).const_mul p))).div
    (((hasDerivAt_sin ((p-1)*t)).comp t ((hasDerivAt_id t).const_mul (p-1))).const_mul Real.pi)
    (mul_ne_zero pi_ne_zero hA)
  have hs : sin (p*t) = sin ((p-1)*t)*cos t + cos ((p-1)*t)*sin t := by
    rw [show p*t = (p-1)*t+t by ring, sin_add]
  have hc : cos (p*t) = cos ((p-1)*t)*cos t - sin ((p-1)*t)*sin t := by
    rw [show p*t = (p-1)*t+t by ring, cos_add]
  have hder : ((cos t * sin (p*t) + sin t * (cos (p*t)*(p*1))) *
      (Real.pi*sin ((p-1)*t)) - sin t*sin (p*t)*(Real.pi*(cos ((p-1)*t)*((p-1)*1)))) /
      (Real.pi*sin ((p-1)*t))^2 =
      (sin (p*t)^2-p*sin t^2)/(Real.pi*sin ((p-1)*t)^2) := by
    have hA' : sin (t*(p-1)) ≠ 0 := by simpa only [mul_comm t (p-1)] using hA
    field_simp [hA, hA', pi_ne_zero]
    rw [mul_comm t (p-1), hs, hc]
    have he := congrArg (fun x : ℝ => p*sin t^2*x) (sin_sq_add_cos_sq ((p-1)*t))
    nlinarith only [he]
  simp only [Function.comp_apply, Pi.mul_apply] at h
  rw [hder] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
  exact angularDensity_at_p hp hx

lemma angularDensity_singlePeak {p : ℝ} (hp : 1 < p) : ∃ t0 ∈ angleInterval p,
    MonotoneOn (angularDensity p p) (Ioo 0 t0) ∧
    AntitoneOn (angularDensity p p) (Ioo t0 (Real.pi/p)) := by
  obtain ⟨t0, ht0, heq⟩ := ratio_crossing hp
  have hp0 : 0 < p := by linarith
  have hsqrt : 0 < sqrt p := sqrt_pos.mpr hp0
  have hs : ∀ t ∈ angleInterval p, 0 < sin t := by
    intro t ht; simpa using sin_scaled_pos hp0 zero_lt_one hp.le ht
  have hsq : ∀ t : ℝ, (sqrt p*sin t)^2 = p*sin t^2 := by
    intro t; rw [mul_pow, sq_sqrt hp0.le]
  have hlow : ∀ t ∈ Ioo 0 t0, 0 ≤ sin (p*t)^2-p*sin t^2 := by
    intro t ht
    have htI : t ∈ angleInterval p := ⟨ht.1, ht.2.trans ht0.2⟩
    have hr := (ratio_strictAntiOn hp htI ht0 ht.2).le
    rw [heq] at hr
    have hge : sqrt p*sin t ≤ sin (p*t) := (le_div_iff₀ (hs t htI)).mp hr
    have hnonneg := mul_pos hsqrt (hs t htI)
    have hsqle := mul_self_le_mul_self hnonneg.le hge
    rw [← sq, ← sq, hsq] at hsqle
    linarith
  have hupp : ∀ t ∈ Ioo t0 (Real.pi/p), sin (p*t)^2-p*sin t^2 ≤ 0 := by
    intro t ht
    have htI : t ∈ angleInterval p := ⟨ht0.1.trans ht.1, ht.2⟩
    have hr := (ratio_strictAntiOn hp ht0 htI ht.1).le
    rw [heq] at hr
    have hle : sin (p*t) ≤ sqrt p*sin t := (div_le_iff₀ (hs t htI)).mp hr
    have hnonneg := sin_scaled_pos hp0 hp0 le_rfl htI
    have hsqle := mul_self_le_mul_self hnonneg.le hle
    rw [← sq, ← sq, hsq] at hsqle
    linarith
  refine ⟨t0, ht0, ?_, ?_⟩
  · apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 t0)
    · intro t ht
      exact (hasDerivAt_angularDensity_at_p hp ⟨ht.1, ht.2.trans ht0.2⟩).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      exact (hasDerivAt_angularDensity_at_p hp ⟨ht.1, ht.2.trans ht0.2⟩).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      rw [(hasDerivAt_angularDensity_at_p hp ⟨ht.1, ht.2.trans ht0.2⟩).deriv]
      exact div_nonneg (hlow t ht) (mul_nonneg pi_pos.le (sq_nonneg _))
  · apply antitoneOn_of_deriv_nonpos (convex_Ioo t0 (Real.pi/p))
    · intro t ht
      exact (hasDerivAt_angularDensity_at_p hp ⟨ht0.1.trans ht.1, ht.2⟩).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      exact (hasDerivAt_angularDensity_at_p hp ⟨ht0.1.trans ht.1, ht.2⟩).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      rw [(hasDerivAt_angularDensity_at_p hp ⟨ht0.1.trans ht.1, ht.2⟩).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (hupp t ht) (mul_nonneg pi_pos.le (sq_nonneg _))

#print axioms angularDensity_singlePeak
#print axioms ratio_crossing
#print axioms hasDerivAt_angularDensity_at_p
end FussCatalan
```

### `FussMeasureSufficient.lean`

```lean
import FussDensityProperties
import FussDensityMonotonicity
import FussCompactification
import FussExceptional

namespace FussCatalan
open Set Real MeasureTheory

lemma density_zero_of_nonpos {p r x : ℝ} (hx : x ≤ 0) : density p r x = 0 := by
  simp [density, show x ∉ Ioo 0 (supportRight p) from fun h => hx.not_gt h.1]

lemma density_antitone_of_angular {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p)
    (hm : MonotoneOn (angularDensity p r) (angleInterval p)) :
    AntitoneOn (density p r) (Ioi 0) := by
  intro x hx y hy hxy
  by_cases hyX : y < supportRight p
  · have hxX : x ∈ Ioo 0 (supportRight p) := ⟨hx, hxy.trans_lt hyX⟩
    have hyX' : y ∈ Ioo 0 (supportRight p) := ⟨hy,hyX⟩
    obtain ⟨s, hs, rfl⟩ := (rho_bijOn hp).surjOn hxX
    obtain ⟨t, ht, rfl⟩ := (rho_bijOn hp).surjOn hyX'
    rw [density_coordinate hp hs, density_coordinate hp ht]
    have hts : t ≤ s := by
      by_contra hnot
      exact (rho_strictAntiOn hp hs ht (lt_of_not_ge hnot)).not_ge hxy
    exact hm ht hs hts
  · have hyout : y ∉ Ioo 0 (supportRight p) := fun h => hyX h.2
    simp only [density, ite_eq_right hyout]
    exact density_nonneg hp hr hrp x

/-- A sufficient bridge to the source's actual measure-level definition. -/
theorem unimodal_of_D_nonneg {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p)
    (hD : ∀ t ∈ angleInterval p, 0 ≤ D p r t) : Unimodal (mu p r) := by
  refine ⟨0, 0, density p r, le_rfl, density_nonneg hp hr hrp,
    density_measurable hp hr hrp, ?_, ?_, ?_⟩
  · intro x hx y hy _
    rw [density_zero_of_nonpos hx.le, density_zero_of_nonpos hy.le]
  · exact density_antitone_of_angular hp hr hrp ((angularDensity_monotone_iff hp hr hrp).mpr hD)
  · simp [mu]

/-- The strict derivative threshold also gives actual unimodality throughout
its closed lower parameter interval. Necessity is not asserted. -/
theorem lower_interval_unimodal {p : ℝ} (hp : 1 < p) :
    ∃ r0 : ℝ, p-1 < r0 ∧ r0 < p ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → Unimodal (mu p r) := by
  obtain ⟨r0, hlow, hupp, hset⟩ := derivative_threshold hp
  refine ⟨r0, hlow, hupp, fun r hr hr0 => ?_⟩
  have hadm : r ∈ admissible p := by rw [hset]; exact ⟨hr,hr0⟩
  exact unimodal_of_D_nonneg hp hr hadm.2.1.le hadm.2.2

lemma rho_order_reflect {p s t : ℝ} (hp : 1 < p) (hs : s ∈ angleInterval p)
    (ht : t ∈ angleInterval p) : rho p s ≤ rho p t ↔ t ≤ s := by
  constructor
  · intro h
    by_contra hnot
    exact (rho_strictAntiOn hp hs ht (lt_of_not_ge hnot)).not_ge h
  · exact (rho_strictAntiOn hp).antitoneOn ht hs

lemma unimodal_of_angular_singlePeak {p r t0 : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p)
    (ht0 : t0 ∈ angleInterval p)
    (hm : MonotoneOn (angularDensity p r) (Ioo 0 t0))
    (ha : AntitoneOn (angularDensity p r) (Ioo t0 (Real.pi/p))) : Unimodal (mu p r) := by
  have hmode := (rho_bijOn hp).mapsTo ht0
  refine ⟨rho p t0, 0, density p r, le_rfl, density_nonneg hp hr hrp,
    density_measurable hp hr hrp, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hy0 : y ≤ 0
    · rw [density_zero_of_nonpos (hxy.trans hy0), density_zero_of_nonpos hy0]
    · have hyX : y ∈ Ioo 0 (supportRight p) := ⟨lt_of_not_ge hy0, hy.trans hmode.2⟩
      by_cases hx0 : x ≤ 0
      · rw [density_zero_of_nonpos hx0]
        exact density_nonneg hp hr hrp y
      · have hxX : x ∈ Ioo 0 (supportRight p) := ⟨lt_of_not_ge hx0, hxy.trans_lt hyX.2⟩
        obtain ⟨s, hs, rfl⟩ := (rho_bijOn hp).surjOn hxX
        obtain ⟨t, ht, rfl⟩ := (rho_bijOn hp).surjOn hyX
        have hs0 : t0 < s := by
          by_contra hh
          exact hx.not_ge ((rho_order_reflect hp ht0 hs).mpr (le_of_not_gt hh))
        have ht0' : t0 < t := by
          by_contra hh
          exact hy.not_ge ((rho_order_reflect hp ht0 ht).mpr (le_of_not_gt hh))
        rw [density_coordinate hp hs, density_coordinate hp ht]
        exact ha ⟨ht0', ht.2⟩ ⟨hs0, hs.2⟩ ((rho_order_reflect hp hs ht).mp hxy)
  · intro x hx y hy hxy
    by_cases hyX : y < supportRight p
    · have hxX : x ∈ Ioo 0 (supportRight p) := ⟨hmode.1.trans hx, hxy.trans_lt hyX⟩
      have hyX' : y ∈ Ioo 0 (supportRight p) := ⟨hmode.1.trans hy, hyX⟩
      obtain ⟨s, hs, rfl⟩ := (rho_bijOn hp).surjOn hxX
      obtain ⟨t, ht, rfl⟩ := (rho_bijOn hp).surjOn hyX'
      have hs0 : s < t0 := by
        by_contra hh
        exact hx.not_ge ((rho_order_reflect hp hs ht0).mpr (le_of_not_gt hh))
      have ht0' : t < t0 := by
        by_contra hh
        exact hy.not_ge ((rho_order_reflect hp ht ht0).mpr (le_of_not_gt hh))
      rw [density_coordinate hp hs, density_coordinate hp ht]
      exact hm ⟨ht.1, ht0'⟩ ⟨hs.1, hs0⟩ ((rho_order_reflect hp hs ht).mp hxy)
    · have hyout : y ∉ Ioo 0 (supportRight p) := fun h => hyX h.2
      simp only [density, ite_eq_right hyout]
      exact density_nonneg hp hr hrp x
  · simp [mu]

theorem unimodal_at_p {p : ℝ} (hp : 1 < p) : Unimodal (mu p p) := by
  obtain ⟨t0, ht0, hm, ha⟩ := angularDensity_singlePeak hp
  exact unimodal_of_angular_singlePeak hp (by linarith) le_rfl ht0 hm ha

#print axioms unimodal_at_p
#print axioms unimodal_of_D_nonneg
#print axioms lower_interval_unimodal
end FussCatalan
```

### `FussMeasureNecessary.lean`

```lean
import FussMeasureSufficient
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.OpenPos

namespace FussCatalan
open Set Real Filter MeasureTheory
open scoped Topology

/-- Continuous functions inherit an order bound from an a.e. bound on an open set. -/
lemma continuousOn_bound_of_ae {f : ℝ → ℝ} {U : Set ℝ} {M : ℝ}
    (hU : IsOpen U) (hf : ContinuousOn f U)
    (hae : ∀ᵐ x ∂volume, x ∈ U → f x ≤ M) : ∀ x ∈ U, f x ≤ M := by
  intro x hx
  by_contra hh
  have hgt : M < f x := lt_of_not_ge hh
  have hn : U ∩ {y | M < f y} ∈ 𝓝 x :=
    inter_mem (hU.mem_nhds hx) ((hf.continuousAt (hU.mem_nhds hx)).eventually (lt_mem_nhds hgt))
  have hd := Measure.dense_of_ae hae
  obtain ⟨y, hy, hye⟩ := mem_closure_iff_nhds.mp (hd x) _ hn
  exact hy.2.not_ge (hye hy.1)

/-- No choice of a monotone a.e. representative can change the order of a continuous density. -/
lemma continuousOn_antitone_of_ae {f g : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (heq : f =ᵐ[volume] g)
    (hg : AntitoneOn g U) : AntitoneOn f U := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with h | h
  · simp [h]
  · by_contra hh
    have hval : f x < f y := lt_of_not_ge hh
    let d := (x+y)/2
    let m := (f x+f y)/2
    have hxd : x < d := by dsimp [d]; linarith
    have hdy : d < y := by dsimp [d]; linarith
    have hxm : f x < m := by dsimp [m]; linarith
    have hmy : m < f y := by dsimp [m]; linarith
    have hnX : (U ∩ Iio d) ∩ {u | f u < m} ∈ 𝓝 x :=
      inter_mem (inter_mem (hU.mem_nhds hx) (Iio_mem_nhds hxd))
        ((hf.continuousAt (hU.mem_nhds hx)).eventually (gt_mem_nhds hxm))
    have hnY : (U ∩ Ioi d) ∩ {v | m < f v} ∈ 𝓝 y :=
      inter_mem (inter_mem (hU.mem_nhds hy) (Ioi_mem_nhds hdy))
        ((hf.continuousAt (hU.mem_nhds hy)).eventually (lt_mem_nhds hmy))
    have hd := Measure.dense_of_ae heq
    obtain ⟨u, hu, hue⟩ := mem_closure_iff_nhds.mp (hd x) _ hnX
    obtain ⟨v, hv, hve⟩ := mem_closure_iff_nhds.mp (hd y) _ hnY
    have horder := hg hu.1.1 hv.1.1 (hu.1.2.trans hv.1.2).le
    change f u = g u at hue
    change f v = g v at hve
    rw [← hue, ← hve] at horder
    have hum : f u < m := hu.2
    have hmv : m < f v := hv.2
    exact (hum.trans hmv).not_ge horder

lemma density_unbounded_near_zero {p r b M : ℝ} (hp : 1 < p) (hr : 0 < r)
    (hrp : r < p) (hb : 0 < b) :
    ∃ x ∈ Ioo 0 (min b (supportRight p)), M < density p r x := by
  have hT : 0 < Real.pi/p := div_pos pi_pos (by linarith)
  have hsmall := (rho_limit_right hp).eventually (gt_mem_nhds hb)
  have hlarge := (angularDensity_blowup hp hr hrp).eventually (eventually_gt_atTop M)
  have hint : ∀ᶠ t in 𝓝[<] (Real.pi/p), t ∈ angleInterval p := Ioo_mem_nhdsLT hT
  obtain ⟨t, ht, hs, hl⟩ := (hint.and (hsmall.and hlarge)).exists
  have hmap := (rho_bijOn hp).mapsTo ht
  refine ⟨rho p t, ⟨hmap.1, lt_min hs hmap.2⟩, ?_⟩
  rwa [density_coordinate hp ht]

lemma unimodal_density_representative {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p)
    (hu : Unimodal (mu p r)) : ∃ b : ℝ, ∃ f : ℝ → ℝ,
      MonotoneOn f (Iio b) ∧ AntitoneOn f (Ioi b) ∧ density p r =ᵐ[volume] f := by
  obtain ⟨b,c,f,hc,hf,hm,hmon,ha,heq⟩ := hu
  have hsingle := congrArg (fun ν : Measure ℝ => ν {b}) heq
  have hz : ENNReal.ofReal c = 0 := by simpa [mu] using hsingle.symm
  have hc0 : c = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hz) hc
  simp only [hc0, ENNReal.ofReal_zero, zero_smul, zero_add] at heq
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (density_measurable hp hr hrp).ennreal_ofReal.aemeasurable hm.ennreal_ofReal.aemeasurable).mp heq
  refine ⟨b,f,hmon,ha,?_⟩
  filter_upwards [hae] with x hx
  have h := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (density_nonneg hp hr hrp x), ENNReal.toReal_ofReal (hf x)] using h

lemma unimodal_implies_D_nonneg {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r < p)
    (hu : Unimodal (mu p r)) : ∀ t ∈ angleInterval p, 0 ≤ D p r t := by
  obtain ⟨b,f,hm,ha,heq⟩ := unimodal_density_representative hp hr hrp.le hu
  have hb : b ≤ 0 := by
    by_contra hh
    have hb0 : 0 < b := lt_of_not_ge hh
    let c := b/2
    have hc0 : 0 < c := half_pos hb0
    have hcb : c < b := half_lt_self hb0
    have haebound : ∀ᵐ x ∂volume, x ∈ Ioo 0 (min c (supportRight p)) → density p r x ≤ f c := by
      filter_upwards [heq] with x hx hxI
      rw [hx]
      exact hm ((hxI.2.trans_le (min_le_left _ _)).trans hcb) hcb (hxI.2.trans_le (min_le_left _ _)).le
    have hbound := continuousOn_bound_of_ae isOpen_Ioo
      ((density_continuousOn hp hr hrp.le).mono (fun x hx => ⟨hx.1,hx.2.trans_le (min_le_right _ _)⟩)) haebound
    obtain ⟨x,hx,hgt⟩ := density_unbounded_near_zero hp hr hrp hc0 (M := f c)
    exact hgt.not_ge (hbound x hx)
  have hanti : AntitoneOn (density p r) (Ioo 0 (supportRight p)) := by
    apply continuousOn_antitone_of_ae isOpen_Ioo (density_continuousOn hp hr hrp.le) heq
    exact ha.mono (fun x hx => hb.trans_lt hx.1)
  apply (angularDensity_monotone_iff hp hr hrp.le).mp
  intro s hs t ht hst
  rw [← density_coordinate hp hs, ← density_coordinate hp ht]
  exact hanti ((rho_bijOn hp).mapsTo ht) ((rho_bijOn hp).mapsTo hs)
    ((rho_strictAntiOn hp).antitoneOn hs ht hst)

theorem unimodal_iff_D_nonneg {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r < p) :
    Unimodal (mu p r) ↔ ∀ t ∈ angleInterval p, 0 ≤ D p r t :=
  ⟨unimodal_implies_D_nonneg hp hr hrp, unimodal_of_D_nonneg hp hr hrp.le⟩

#print axioms unimodal_iff_D_nonneg
end FussCatalan
```

### `FussMeasureBasics.lean`

```lean
import FussMeasureNecessary

namespace FussCatalan
open Set Real Filter MeasureTheory
open scoped ENNReal

lemma mu_supported (p r : ℝ) : mu p r (Icc 0 (supportRight p))ᶜ = 0 := by
  rw [mu, withDensity_apply _ isClosed_Icc.measurableSet.compl]
  calc
    _ = ∫⁻ _x : ℝ, (0 : ENNReal) ∂(volume.restrict ((Icc 0 (supportRight p))ᶜ)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet.compl] with x hx
      have hx' : x ∉ Ioo 0 (supportRight p) := fun h => hx ⟨h.1.le,h.2.le⟩
      simp [density, hx']
    _ = 0 := by simp

/-- Positivity is proved without presupposing a probability instance. -/
lemma mu_ne_zero {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hrp : r ≤ p) : mu p r ≠ 0 := by
  intro hz
  have hae := (withDensity_eq_zero_iff (density_measurable hp hr hrp).ennreal_ofReal.aemeasurable).mp hz
  have hbound : ∀ᵐ x ∂volume, x ∈ Ioo 0 (supportRight p) → density p r x ≤ 0 := by
    filter_upwards [hae] with x hx _
    exact ENNReal.ofReal_eq_zero.mp hx
  have hpoint := continuousOn_bound_of_ae isOpen_Ioo (density_continuousOn hp hr hrp) hbound
  have hT : 0 < Real.pi/p := div_pos pi_pos (by linarith)
  have ht : (Real.pi/p)/2 ∈ angleInterval p := ⟨half_pos hT, half_lt_self hT⟩
  have hle := hpoint (rho p ((Real.pi/p)/2)) ((rho_bijOn hp).mapsTo ht)
  rw [density_coordinate hp ht] at hle
  exact (angularDensity_pos hp hr hrp ht).not_ge hle

#print axioms mu_supported
#print axioms mu_ne_zero
end FussCatalan
```

### `FussStage2.lean`

```lean
import FussMeasureNecessary

namespace FussCatalan
open Set MeasureTheory

/-- Root's density-defined endpoint, including the still-required normalization. -/
def DensityConjecture : Prop :=
  (∀ p r : ℝ, 1 < p → 0 < r → r ≤ p → IsProbabilityMeasure (mu p r)) ∧
  ∀ p : ℝ, 1 < p → ∃ r0 : ℝ, p-1 < r0 ∧ r0 < p ∧
    ∀ r : ℝ, 0 < r → r ≤ p → (Unimodal (mu p r) ↔ r = p ∨ r ≤ r0)

/-- Full measure-level classification for the exact explicit-density measure.
This does not assert probability normalization or a moment identity. -/
theorem density_measure_phase_transition :
    ∀ p : ℝ, 1 < p → ∃ r0 : ℝ, p-1 < r0 ∧ r0 < p ∧
      ∀ r : ℝ, 0 < r → r ≤ p → (Unimodal (mu p r) ↔ r = p ∨ r ≤ r0) := by
  intro p hp
  obtain ⟨r0, hl, hu, hset⟩ := derivative_threshold hp
  refine ⟨r0, hl, hu, fun r hr hrp => ?_⟩
  by_cases heq : r = p
  · subst r
    exact iff_of_true (unimodal_at_p hp) (Or.inl rfl)
  · have hlt : r < p := lt_of_le_of_ne hrp heq
    rw [unimodal_iff_D_nonneg hp hr hlt]
    have hiff : (∀ t ∈ angleInterval p, 0 ≤ D p r t) ↔ r ∈ admissible p :=
      ⟨fun h => ⟨hr,hlt,h⟩, fun h => h.2.2⟩
    rw [hiff, hset]
    simp only [mem_Ioc, hr, true_and, heq, false_or]

/-- The only remaining conjunct of the designed endpoint is probability normalization. -/
theorem densityConjecture_iff_normalization :
    DensityConjecture ↔
      ∀ p r : ℝ, 1 < p → 0 < r → r ≤ p → IsProbabilityMeasure (mu p r) :=
  ⟨And.left, fun hn => ⟨hn, density_measure_phase_transition⟩⟩

#print axioms density_measure_phase_transition
#print axioms densityConjecture_iff_normalization
end FussCatalan
```

### `FussPacket.lean`

```lean
import FussStage2
import FussMeasureBasics

namespace FussCatalan
#eval Lean.versionString
#print DensityConjecture
#check raneyMoment_zero
#print axioms raneyMoment_zero
#check raneyMoment_one
#print axioms raneyMoment_one
#check density_coordinate_of_bijOn
#print axioms density_coordinate_of_bijOn
#check sin_mul_cos_lt
#print axioms sin_mul_cos_lt
#check hasDerivAt_mul_cot
#print axioms hasDerivAt_mul_cot
#check strictAntiOn_mul_cot
#print axioms strictAntiOn_mul_cot
#check scaled_cot_lt
#print axioms scaled_cot_lt
#check scaled_angle_pos_lt_pi
#print axioms scaled_angle_pos_lt_pi
#check sin_scaled_pos
#print axioms sin_scaled_pos
#check D_affine
#print axioms D_affine
#check D_strictAnti_parameter
#print axioms D_strictAnti_parameter
#check admissible_downward
#print axioms admissible_downward
#check continuousAt_parameter_D
#print axioms continuousAt_parameter_D
#check admissible_closed_inside
#print axioms admissible_closed_inside
#check threshold_of_order_closed
#print axioms threshold_of_order_closed
#check compact_slice_positive
#print axioms compact_slice_positive
#check cot_add_identity
#print axioms cot_add_identity
#check D_at_p_sub_one_pos
#print axioms D_at_p_sub_one_pos
#check p_sub_one_mem_admissible
#print axioms p_sub_one_mem_admissible
#check mem_admissible_of_le_p_sub_one
#print axioms mem_admissible_of_le_p_sub_one
#check derivative_threshold_of_bounds
#print axioms derivative_threshold_of_bounds
#check angularDensity_pos
#print axioms angularDensity_pos
#check log_angularDensity
#print axioms log_angularDensity
#check hasDerivAt_log_sin_scaled
#print axioms hasDerivAt_log_sin_scaled
#check hasDerivAt_logAngular
#print axioms hasDerivAt_logAngular
#check hasDerivAt_log_angularDensity
#print axioms hasDerivAt_log_angularDensity
#check angularDensity_monotone_iff
#print axioms angularDensity_monotone_iff
#check angularDensity_monotone_lower_range
#print axioms angularDensity_monotone_lower_range
#check supportRight_pos
#print axioms supportRight_pos
#check angularDensity_continuousOn
#print axioms angularDensity_continuousOn
#check rho_pos
#print axioms rho_pos
#check log_rho
#print axioms log_rho
#check hasDerivAt_log_rho
#print axioms hasDerivAt_log_rho
#check rho_strictAntiOn
#print axioms rho_strictAntiOn
#check rho_continuousOn
#print axioms rho_continuousOn
#check rho_sinc
#print axioms rho_sinc
#check rho_limit_left
#print axioms rho_limit_left
#check rho_limit_right
#print axioms rho_limit_right
#check rho_bijOn
#print axioms rho_bijOn
#check density_coordinate
#print axioms density_coordinate
#check density_nonneg
#print axioms density_nonneg
#check inverse_rho_strictAntiOn
#print axioms inverse_rho_strictAntiOn
#check inverse_rho_continuousOn
#print axioms inverse_rho_continuousOn
#check density_continuousOn
#print axioms density_continuousOn
#check density_measurable
#print axioms density_measurable
#check angle_top_factors
#print axioms angle_top_factors
#check cot_at_angle_top
#print axioms cot_at_angle_top
#check D_at_p_tendsto
#print axioms D_at_p_tendsto
#check D_at_p_negative
#print axioms D_at_p_negative
#check admissible_strict_upper
#print axioms admissible_strict_upper
#check angularDensity_blowup
#print axioms angularDensity_blowup
#check angularDensity_at_p
#print axioms angularDensity_at_p
#check angularDensity_at_p_limit_right
#print axioms angularDensity_at_p_limit_right
#check qcot_zero
#print axioms qcot_zero
#check qcot_eq
#print axioms qcot_eq
#check continuousAt_qcot
#print axioms continuousAt_qcot
#check compactD_eq
#print axioms compactD_eq
#check compactD_zero
#print axioms compactD_zero
#check compactD_top
#print axioms compactD_top
#check compactLeft_eq
#print axioms compactLeft_eq
#check compactRight_eq
#print axioms compactRight_eq
#check compactD_continuous_slice
#print axioms compactD_continuous_slice
#check admissible_strict_lower
#print axioms admissible_strict_lower
#check derivative_threshold
#print axioms derivative_threshold
#check sineRatio_pos
#print axioms sineRatio_pos
#check hasDerivAt_log_sineRatio
#print axioms hasDerivAt_log_sineRatio
#check ratio_strictAntiOn
#print axioms ratio_strictAntiOn
#check sineRatio_continuousOn
#print axioms sineRatio_continuousOn
#check sineRatio_limit_left
#print axioms sineRatio_limit_left
#check sineRatio_limit_right
#print axioms sineRatio_limit_right
#check ratio_crossing
#print axioms ratio_crossing
#check hasDerivAt_angularDensity_at_p
#print axioms hasDerivAt_angularDensity_at_p
#check angularDensity_singlePeak
#print axioms angularDensity_singlePeak
#check density_zero_of_nonpos
#print axioms density_zero_of_nonpos
#check density_antitone_of_angular
#print axioms density_antitone_of_angular
#check unimodal_of_D_nonneg
#print axioms unimodal_of_D_nonneg
#check lower_interval_unimodal
#print axioms lower_interval_unimodal
#check rho_order_reflect
#print axioms rho_order_reflect
#check unimodal_of_angular_singlePeak
#print axioms unimodal_of_angular_singlePeak
#check unimodal_at_p
#print axioms unimodal_at_p
#check continuousOn_bound_of_ae
#print axioms continuousOn_bound_of_ae
#check continuousOn_antitone_of_ae
#print axioms continuousOn_antitone_of_ae
#check density_unbounded_near_zero
#print axioms density_unbounded_near_zero
#check unimodal_density_representative
#print axioms unimodal_density_representative
#check unimodal_implies_D_nonneg
#print axioms unimodal_implies_D_nonneg
#check unimodal_iff_D_nonneg
#print axioms unimodal_iff_D_nonneg
#check mu_supported
#print axioms mu_supported
#check mu_ne_zero
#print axioms mu_ne_zero
#check density_measure_phase_transition
#print axioms density_measure_phase_transition
#check densityConjecture_iff_normalization
#print axioms densityConjecture_iff_normalization
end FussCatalan
```

