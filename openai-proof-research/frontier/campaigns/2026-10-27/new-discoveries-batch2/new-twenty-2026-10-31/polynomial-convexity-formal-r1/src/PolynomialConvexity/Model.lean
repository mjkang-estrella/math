import PolynomialConvexity.Convexity
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-! Concrete probability-space construction. This module does NOT prove the
mixed-moment identity or its integrability; see SUMMARY.md for open bridges. -/
namespace PolynomialConvexity
noncomputable section
open MeasureTheory ProbabilityTheory Finset

def clockMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => expMeasure 1)

instance clockMeasure_probability (n : ℕ) : IsProbabilityMeasure (clockMeasure n) := by
  have : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  unfold clockMeasure
  infer_instance

theorem clocks_independent (n : ℕ) :
    iIndepFun (fun i : Fin n => fun ω : Fin n → ℝ => ω i) (clockMeasure n) := by
  have : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

theorem edge_nonempty {n L : ℕ} (hL : 0 < L) (e : Edge n L) : e.val.Nonempty := by
  apply card_pos.mp
  rw [e.property]
  exact hL

def lifetime {n L : ℕ} (hL : 0 < L) (e : Edge n L) (ω : Fin n → ℝ) : ℝ :=
  e.val.inf' (edge_nonempty hL e) ω

theorem lifetime_measurable {n L : ℕ} (hL : 0 < L) (e : Edge n L) :
    Measurable (lifetime hL e) := by
  unfold lifetime
  exact (Continuous.finset_inf'_apply (edge_nonempty hL e)
    (fun v _ => continuous_apply v)).measurable

theorem lifetime_nonneg {n L : ℕ} (hL : 0 < L) (e : Edge n L)
    (ω : Fin n → ℝ) (hω : ∀ v, 0 ≤ ω v) : 0 ≤ lifetime hL e ω := by
  exact (le_inf'_iff _ _).2 (fun v _ => hω v)

theorem lifetime_le_clock {n L : ℕ} (hL : 0 < L) (e : Edge n L)
    (ω : Fin n → ℝ) (v : Fin n) (hv : v ∈ e.val) : lifetime hL e ω ≤ ω v := by
  exact inf'_le ω hv

/-- Repeated edges use the same minimum, never independent copies. -/
theorem lifetime_threshold {n L : ℕ} (hL : 0 < L) (e : Edge n L)
    (ω : Fin n → ℝ) (t : ℝ) :
    t ≤ lifetime hL e ω ↔ ∀ v ∈ e.val, t ≤ ω v :=
  le_inf'_iff _ _

/-- The baseline 0 also constrains vertices absent from all tuple edges. -/
def vertexThreshold {n L d : ℕ} (e : Fin d → Edge n L)
    (t : Fin d → ℝ) (v : Fin n) : ℝ :=
  univ.sup' univ_nonempty (fun o : Option (Fin d) =>
    match o with
    | none => 0
    | some i => if v ∈ (e i).val then t i else 0)

theorem vertexThreshold_le {n L d : ℕ} (e : Fin d → Edge n L)
    (t : Fin d → ℝ) (v : Fin n) (r : ℝ) :
    vertexThreshold e t v ≤ r ↔ 0 ≤ r ∧ ∀ i, v ∈ (e i).val → t i ≤ r := by
  simp only [vertexThreshold, sup'_le_iff, mem_univ, forall_true_left]
  constructor
  · intro h
    refine ⟨h none, fun i hi => ?_⟩
    simpa [hi] using h (some i)
  · rintro ⟨hr, h⟩ o
    cases o with
    | none => exact hr
    | some i =>
      by_cases hv : v ∈ (e i).val
      · simpa [hv] using h i hv
      · simpa [hv] using hr

/-- Exact joint-survival event as a rectangle, intersected with clock support. -/
theorem joint_event_rectangle {n L d : ℕ} (hL : 0 < L)
    (e : Fin d → Edge n L) (t : Fin d → ℝ) :
    {ω : Fin n → ℝ | (∀ v, 0 ≤ ω v) ∧ ∀ i, t i ≤ lifetime hL (e i) ω} =
      Set.pi Set.univ (fun v => Set.Ici (vertexThreshold e t v)) := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Ici, vertexThreshold_le, lifetime_threshold]
  constructor
  · rintro ⟨hω, h⟩ v
    exact ⟨hω v, fun i hv => h i v hv⟩
  · intro h
    exact ⟨fun v => (h v).1, fun i v hv => (h v).2 i hv⟩

theorem joint_event_probability {n L d : ℕ} (hL : 0 < L)
    (e : Fin d → Edge n L) (t : Fin d → ℝ) :
    clockMeasure n {ω | (∀ v, 0 ≤ ω v) ∧ ∀ i, t i ≤ lifetime hL (e i) ω} =
      ∏ v, expMeasure 1 (Set.Ici (vertexThreshold e t v)) := by
  have : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  rw [joint_event_rectangle]
  exact Measure.pi_pi _ _

end
end PolynomialConvexity
