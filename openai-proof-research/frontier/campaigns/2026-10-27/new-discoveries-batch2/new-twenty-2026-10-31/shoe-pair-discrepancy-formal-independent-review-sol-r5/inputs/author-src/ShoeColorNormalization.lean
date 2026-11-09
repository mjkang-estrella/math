import ShoeColorEndpoint

namespace Shoe
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

theorem color_nontermination_probability_zero (p : PMF α) :
    colorSampleMeasure p {ω | ¬ Terminates ω} = 0 := by
  obtain ⟨e,he⟩ := exists_injective_nat α
  have h := nontermination_probability_zero (p.map e)
  change sampleMeasure (p.map e) ({ω | Terminates ω}ᶜ) = 0 at h
  rw [colorSampleMeasure_coded_apply p e _ measurable_terminates.compl] at h
  have hs : relabelSample e ⁻¹' ({ω | Terminates ω}ᶜ) =
      {ω : Sample α | ¬ Terminates ω} := by
    ext ω
    exact not_congr (terminates_relabel_iff e he ω)
  rwa [hs] at h

theorem color_ae_terminates (p : PMF α) :
    ∀ᵐ ω ∂colorSampleMeasure p, Terminates ω := by
  rw [ae_iff]
  exact color_nontermination_probability_zero p

instance colorConditionalMeasure_probability (p : PMF α) :
    IsProbabilityMeasure (colorConditionalMeasure p) := by
  obtain ⟨e,he⟩ := exists_injective_nat α
  constructor
  have h := congrArg (fun μ : Measure ℕ => μ Set.univ)
    (colorConditionalMeasure_transport p e he)
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ,
    Set.preimage_univ] at h
  exact h.trans (measure_univ)

instance colorWinner_probability (p : PMF α) (c : α) :
    IsProbabilityMeasure ((colorSampleMeasure p).map (colorWinner c)) := by
  constructor
  rw [Measure.map_apply (measurable_colorWinner c) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

theorem color_fallback_ae (p : PMF α) (c d : α) :
    colorWinner c =ᵐ[colorSampleMeasure p] colorWinner d := by
  filter_upwards [color_ae_terminates p] with ω hω
  simp only [colorWinner, dite_eq_left hω]

end Shoe
