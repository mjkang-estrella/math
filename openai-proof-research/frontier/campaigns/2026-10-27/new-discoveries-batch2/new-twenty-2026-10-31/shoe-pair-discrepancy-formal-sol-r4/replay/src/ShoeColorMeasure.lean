import ShoeRelabel
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace Shoe
open MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The same infinite iid construction on any countable discrete alphabet. -/
noncomputable def colorSampleMeasure {α : Type*} [MeasurableSpace α]
    (p : PMF α) : Measure (Sample α) :=
  Measure.infinitePi (fun _ : ℕ => p.toMeasure)

instance colorSampleMeasure_probability {α : Type*} [MeasurableSpace α]
    (p : PMF α) : IsProbabilityMeasure (colorSampleMeasure p) := by
  unfold colorSampleMeasure
  infer_instance

theorem measurable_relabelSample {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (e : α → β) (he : Measurable e) :
    Measurable (relabelSample e) := by
  exact Measurable.of_eval (fun n => he.comp (measurable_pi_apply n))

/-- Coordinatewise coding pushes the actual iid product measure forward.
Injectivity is unnecessary for this probability identity; it is needed for
chronological matching, as proved in ShoeRelabel. -/
theorem colorSampleMeasure_map {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (p : PMF α) (e : α → β) (he : Measurable e) :
    (colorSampleMeasure p).map (relabelSample e) = colorSampleMeasure (p.map e) := by
  unfold colorSampleMeasure relabelSample
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => p.toMeasure) (fun _ => he)]
  simp only [PMF.toMeasure_map e p he]

theorem colorSampleMeasure_nat (p : PMF ℕ) : colorSampleMeasure p = sampleMeasure p := rfl

/-- Explicit fallback transported along with colors, including nontermination.
It agrees with the source winner on the terminating event. -/
noncomputable def colorWinner {α : Type*} (fallback : α) (ω : Sample α) : α :=
  if h : Terminates ω then ω (firstLength ω h - 1) else fallback

theorem colorWinner_relabel {α β : Type*} (e : α → β) (he : Function.Injective e)
    (fallback : α) (ω : Sample α) :
    colorWinner (e fallback) (relabelSample e ω) = e (colorWinner fallback ω) := by
  by_cases ht : Terminates ω
  · have hte := (terminates_relabel_iff e he ω).mpr ht
    simp only [colorWinner, dite_eq_left ht, dite_eq_left hte,
      firstLength_relabel e he ω ht, relabelSample]
  · have hte : ¬ Terminates (relabelSample e ω) :=
      fun h => ht ((terminates_relabel_iff e he ω).mp h)
    simp only [colorWinner, dite_eq_right ht, dite_eq_right hte]

/-- Finite zero extension is the PMF pushforward, with the same product space
and chronological winner transport; no full-support restriction occurs. -/
theorem finite_colorSampleMeasure_map (n : ℕ) (p : PMF (Fin n)) :
    (colorSampleMeasure p).map (relabelSample Fin.val) =
      sampleMeasure (p.map Fin.val) := by
  exact colorSampleMeasure_map p Fin.val (measurable_of_countable _)

end Shoe
