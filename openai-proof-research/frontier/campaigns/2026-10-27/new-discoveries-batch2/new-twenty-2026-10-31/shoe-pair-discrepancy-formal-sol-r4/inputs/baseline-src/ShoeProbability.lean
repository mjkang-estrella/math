import ShoeBase
import Mathlib.Probability.ProductMeasure

namespace Shoe
open MeasureTheory
open scoped ENNReal

/-- Independent chronological shoes. Nat colors include infinite support and
finite laws padded by zero. All time coordinates have exactly the same law. -/
noncomputable def sampleMeasure (p : DiscreteLaw ℕ) : Measure (Sample ℕ) :=
  Measure.infinitePi (fun _ : ℕ => p.toMeasure)

instance sampleMeasure_probability (p : DiscreteLaw ℕ) :
    IsProbabilityMeasure (sampleMeasure p) := by
  unfold sampleMeasure
  infer_instance

/-- The full finite-cylinder product law, with arbitrary measurable restrictions. -/
theorem cylinder_probability (p : DiscreteLaw ℕ) (s : Finset ℕ)
    (t : ℕ → Set ℕ) (ht : ∀ j ∈ s, MeasurableSet (t j)) :
    sampleMeasure p (Set.pi (s : Set ℕ) t) = ∏ j ∈ s, p.toMeasure (t j) := by
  exact Measure.infinitePi_pi (fun _ : ℕ => p.toMeasure) ht

theorem coordinate_law (p : DiscreteLaw ℕ) (j : ℕ) :
    (sampleMeasure p).map (fun ω => ω j) = p.toMeasure :=
  Measure.infinitePi_map_eval (fun _ : ℕ => p.toMeasure) j

theorem coordinate_color (p : DiscreteLaw ℕ) (j i : ℕ) :
    sampleMeasure p {ω | ω j = i} = p i := by
  have h := congrArg (fun μ : Measure ℕ => μ {i}) (coordinate_law p j)
  rw [Measure.map_apply (measurable_pi_apply j) (measurableSet_singleton i),
    p.toMeasure_apply_singleton i (measurableSet_singleton i)] at h
  exact h

theorem measurable_hasMatch (n : ℕ) : MeasurableSet {ω : Sample ℕ | HasMatch ω n} := by
  have he (a b : ℕ) : MeasurableSet {ω : Sample ℕ | ω (2*a) = ω (2*b+1)} :=
    measurableSet_eq_fun (measurable_pi_apply _) (measurable_pi_apply _)
  simp only [HasMatch, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  by_cases ha : 2*a < n
  · by_cases hb : 2*b+1 < n
    · simpa only [ha, hb, true_and] using he a b
    · simp only [hb, and_false, false_and, Set.ofPred_false, MeasurableSet.empty]
  · simp only [ha, false_and, Set.ofPred_false, MeasurableSet.empty]

theorem measurable_firstMatch (n : ℕ) :
    MeasurableSet {ω : Sample ℕ | FirstMatch ω n} :=
  (measurable_hasMatch (n+1)).inter (measurable_hasMatch n).compl

theorem measurable_terminates : MeasurableSet {ω : Sample ℕ | Terminates ω} := by
  simp only [Terminates, Set.ofPred_exists]
  exact MeasurableSet.iUnion measurable_hasMatch

end Shoe
