import ShoeSourceTV
import ShoeConditional
import ShoeTermination

namespace Shoe
open MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def sourceX (p : DiscreteLaw ℕ) : PMF ℕ :=
  (conditionalColorMeasure p).toPMF

noncomputable def sourceWinner (c : ℕ) (ω : Sample ℕ) : ℕ :=
  if Terminates ω then winner ω else c

theorem measurable_sourceWinner (c : ℕ) : Measurable (sourceWinner c) := by
  exact Measurable.ite measurable_terminates measurable_winner measurable_const

instance sourceWinner_probability (p : DiscreteLaw ℕ) (c : ℕ) :
    IsProbabilityMeasure ((sampleMeasure p).map (sourceWinner c)) := by
  constructor
  rw [Measure.map_apply (measurable_sourceWinner c) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

noncomputable def sourceY (p : DiscreteLaw ℕ) (c : ℕ) : PMF ℕ :=
  ((sampleMeasure p).map (sourceWinner c)).toPMF

theorem sourceY_eq (p : DiscreteLaw ℕ) (c : ℕ) : sourceY p c = winningLaw p := by
  apply PMF.ext
  intro i
  unfold sourceY winningLaw
  rw [Measure.toPMF_apply, Measure.toPMF_apply]
  congr 1
  exact Measure.map_congr (fallback_ae p c)

noncomputable def sourceDiscrepancy (p : DiscreteLaw ℕ) (fallback : ℕ) : ℝ :=
  sourceTV (sourceX p) (sourceY p fallback)

theorem sourceDiscrepancy_bound (p : DiscreteLaw ℕ) (fallback : ℕ) :
    sourceDiscrepancy p fallback ≤ 255/256 := by
  unfold sourceDiscrepancy sourceX
  rw [conditionalColorMeasure_toPMF, sourceY_eq]
  exact source_discrepancy_uniform p

/-- The same constant bounds the entire supremum of source discrepancies. -/
theorem source_strict_universal_supremum (fallback : ℕ) :
    sSup (Set.range (fun p : DiscreteLaw ℕ => sourceDiscrepancy p fallback)) ≤ 255/256 ∧
    sSup (Set.range (fun p : DiscreteLaw ℕ => sourceDiscrepancy p fallback)) < 1 := by
  have h : sSup (Set.range (fun p : DiscreteLaw ℕ => sourceDiscrepancy p fallback)) ≤
      255/256 := by
    apply csSup_le
    · exact ⟨_,⟨PMF.pure 0,rfl⟩⟩
    · rintro _ ⟨p,rfl⟩
      exact sourceDiscrepancy_bound p fallback
  exact ⟨h,lt_of_le_of_lt h (by norm_num)⟩

end Shoe
