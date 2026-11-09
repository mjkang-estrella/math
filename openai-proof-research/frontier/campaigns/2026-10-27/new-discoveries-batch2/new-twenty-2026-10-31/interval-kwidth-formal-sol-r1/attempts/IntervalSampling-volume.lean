import IntervalThreshold
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi

namespace IntervalWidth
open MeasureTheory

/-- Exactly 2n endpoint coordinates, in the original sampling order. -/
abbrev Samples (n : Nat) := Fin n × Fin 2 → ℝ

/-- Uniform(0,1), written as Lebesgue restriction (the interval has length one). -/
noncomputable def uniformEndpoint : Measure ℝ := volume.restrict (Set.Ioo 0 1)

instance uniformEndpoint_probability : IsProbabilityMeasure uniformEndpoint := by
  constructor
  simp [uniformEndpoint, Real.volume_Ioo]

/-- The actual finite product measure, not a discretization of endpoint ranks. -/
noncomputable def sampleMeasure (n : Nat) : Measure (Samples n) :=
  Measure.pi (fun _ : Fin n × Fin 2 => uniformEndpoint)

instance sampleMeasure_probability (n : Nat) : IsProbabilityMeasure (sampleMeasure n) := by
  unfold sampleMeasure
  infer_instance

noncomputable def sampledIntervals {n : Nat} (ω : Samples n) (i : Fin n) : Interval ℝ :=
  ⟨min (ω (i,0)) (ω (i,1)), max (ω (i,0)) (ω (i,1))⟩

theorem sampled_valid {n : Nat} (ω : Samples n) (i : Fin n) :
    (sampledIntervals ω i).left ≤ (sampledIntervals ω i).right :=
  min_le_max

theorem measurable_sample_left {n : Nat} (i : Fin n) :
    Measurable (fun ω : Samples n => (sampledIntervals ω i).left) :=
  (measurable_pi_apply (i,0)).min (measurable_pi_apply (i,1))

theorem measurable_sample_right {n : Nat} (i : Fin n) :
    Measurable (fun ω : Samples n => (sampledIntervals ω i).right) :=
  (measurable_pi_apply (i,0)).max (measurable_pi_apply (i,1))

end IntervalWidth
