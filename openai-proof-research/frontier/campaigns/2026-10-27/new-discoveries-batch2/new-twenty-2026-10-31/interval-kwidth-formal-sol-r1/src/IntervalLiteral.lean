import IntervalSampling
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace IntervalWidth
open MeasureTheory Filter
open scoped Topology

/-- Actual expectation of the source tree-partition width; no finitary proxy. -/
noncomputable def expectedWidth (k n : Nat) : ℝ :=
  ∫ ω : Samples n, (width k (sampledIntervals ω) : ℝ) ∂sampleMeasure n

/-- The exact MathDB 336276 endpoint. This Prop is defined, NOT yet proved. -/
def LiteralStatement : Prop :=
  ∀ k : Nat, 2 ≤ k → ∃ c : ℝ, 0 < c ∧
    Tendsto (fun n : Nat => expectedWidth k n / (n : ℝ)) atTop (nhds c) ∧
    c = 1 / ((k : ℝ) + 1)

end IntervalWidth
