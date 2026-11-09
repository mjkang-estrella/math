import ShoeColorWinner

namespace Shoe
open MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable
variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- Conditional iid pair color, normalized by the actual equality event. -/
noncomputable def colorConditionalMeasure (p : PMF α) : Measure α :=
  (colorSampleMeasure p {ω | ω 0 = ω 1})⁻¹ •
    (((colorSampleMeasure p).restrict {ω | ω 0 = ω 1}).map (fun ω => ω 0))

theorem colorSampleMeasure_coded_apply (p : PMF α) (e : α → ℕ)
    (S : Set (Sample ℕ)) (hS : MeasurableSet S) :
    sampleMeasure (p.map e) S = colorSampleMeasure p (relabelSample e ⁻¹' S) := by
  rw [← colorSampleMeasure_nat, ← colorSampleMeasure_map p e (measurable_of_countable _),
    Measure.map_apply (measurable_relabelSample e (measurable_of_countable _)) hS]

theorem color_pair_equality_transport (p : PMF α) (e : α → ℕ)
    (he : Function.Injective e) :
    colorSampleMeasure p {ω | ω 0 = ω 1} = collisionMass (p.map e) := by
  rw [← pair_equality_probability, colorSampleMeasure_coded_apply p e _
    (measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1))]
  congr 1
  ext ω
  exact (he.eq_iff).symm

theorem colorConditionalMeasure_transport (p : PMF α) (e : α → ℕ)
    (he : Function.Injective e) :
    (colorConditionalMeasure p).map e = conditionalColorMeasure (p.map e) := by
  have hm : Measurable e := measurable_of_countable _
  unfold colorConditionalMeasure conditionalColorMeasure
  rw [color_pair_equality_transport p e he, Measure.map_smul _ hm.aemeasurable,
    Measure.map_map hm (measurable_pi_apply 0)]
  congr 1
  ext B hB : 1
  rw [Measure.map_apply (hm.comp (measurable_pi_apply 0)) hB,
    Measure.restrict_apply ((hm.comp (measurable_pi_apply 0)) hB),
    Measure.map_apply (measurable_pi_apply 0) hB,
    Measure.restrict_apply ((measurable_pi_apply 0) hB)]
  rw [colorSampleMeasure_coded_apply p e _
    (((measurable_pi_apply 0) hB).inter
      (measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1)))]
  congr 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
    Function.comp_apply, relabelSample, he.eq_iff]

end Shoe
