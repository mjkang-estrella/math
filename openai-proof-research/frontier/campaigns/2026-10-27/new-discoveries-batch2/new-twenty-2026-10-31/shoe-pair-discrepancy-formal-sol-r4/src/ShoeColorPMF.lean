import ShoeColorNormalization

namespace Shoe
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

theorem colorConditional_toPMF_transport (p : PMF α) (e : α → ℕ)
    (he : Function.Injective e) :
    ((colorConditionalMeasure p).toPMF).map e = sourceX (p.map e) := by
  apply PMF.toMeasure_inj.mp
  rw [← PMF.toMeasure_map e _ (measurable_of_countable _), Measure.toPMF_toMeasure]
  unfold sourceX
  rw [Measure.toPMF_toMeasure, colorConditionalMeasure_transport p e he]

theorem colorWinner_toPMF_transport (p : PMF α) (c : α) (e : α → ℕ)
    (he : Function.Injective e) :
    (((colorSampleMeasure p).map (colorWinner c)).toPMF).map e =
      sourceY (p.map e) (e c) := by
  apply PMF.toMeasure_inj.mp
  rw [← PMF.toMeasure_map e _ (measurable_of_countable _), Measure.toPMF_toMeasure]
  unfold sourceY
  rw [Measure.toPMF_toMeasure, colorWinner_measure_transport p c e he]

end Shoe
