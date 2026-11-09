import ClockMarginals
import FiniteCore
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
namespace MedianClock
theorem initial_mass_literal (s : MedianTemporal.Config) :
    initialLaw.real {s} = MedianTemporal.weight s / (5:ℝ)^10 := initial_mass s
/-- An independent count and an iid mark prefix. No clock realization is asserted. -/
noncomputable def markedLaw (q : Measure ℕ) (k : ℕ) := q.prod (prefixLaw k)
instance (q : Measure ℕ) [IsProbabilityMeasure q] (k : ℕ) :
    IsProbabilityMeasure (markedLaw q k) := by unfold markedLaw; infer_instance

theorem marked_rectangles (q : Measure ℕ) [IsProbabilityMeasure q] (k : ℕ)
    (a : Set ℕ) (b : Set (Fin k → Vertex)) :
    markedLaw q k (a ×ˢ b) = q a * prefixLaw k b := Measure.prod_prod a b

theorem marked_mass (q : Measure ℕ) [IsProbabilityMeasure q] (k : ℕ)
    (w : Fin k → Vertex) :
    (markedLaw q k).real ({k} ×ˢ {w}) = q.real {k} * (1/10:ℝ)^k := by
  change (markedLaw q k ({k} ×ˢ {w})).toReal = _
  rw [marked_rectangles, ENNReal.toReal_mul]
  exact congrArg (fun x : ℝ => q.real {k} * x) (prefix_mass k w)

noncomputable def initializedLaw (q : Measure ℕ) (k : ℕ) := initialLaw.prod (markedLaw q k)
instance (q : Measure ℕ) [IsProbabilityMeasure q] (k : ℕ) :
    IsProbabilityMeasure (initializedLaw q k) := by unfold initializedLaw; infer_instance

theorem initialized_rectangles (q : Measure ℕ) [IsProbabilityMeasure q] (k : ℕ)
    (a : Set Config) (b : Set (ℕ × (Fin k → Vertex))) :
    initializedLaw q k (a ×ˢ b) = initialLaw a * markedLaw q k b := Measure.prod_prod a b

theorem initialized_mass (q : Measure ℕ) [IsProbabilityMeasure q] (k : ℕ)
    (s : Config) (w : Fin k → Vertex) :
    (initializedLaw q k).real ({s} ×ˢ ({k} ×ˢ {w})) =
      (weight s / (5:ℝ)^10) * (q.real {k} * (1/10:ℝ)^k) := by
  change (initializedLaw q k ({s} ×ˢ ({k} ×ˢ {w}))).toReal = _
  rw [initialized_rectangles, ENNReal.toReal_mul]
  change initialLaw.real {s} * (markedLaw q k).real ({k} ×ˢ {w}) = _
  rw [initial_mass, marked_mass]
end MedianClock
