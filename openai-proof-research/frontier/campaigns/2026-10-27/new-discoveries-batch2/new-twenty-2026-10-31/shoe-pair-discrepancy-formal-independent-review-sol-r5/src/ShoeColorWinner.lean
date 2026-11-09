import ShoeColorMeasure

namespace Shoe
open MeasureTheory
attribute [local instance] Classical.propDecidable

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

theorem measurable_colorHasMatch (n : ℕ) :
    MeasurableSet {ω : Sample α | HasMatch ω n} := by
  have he (a b : ℕ) : MeasurableSet {ω : Sample α | ω (2*a) = ω (2*b+1)} :=
    measurableSet_eq_fun (measurable_pi_apply _) (measurable_pi_apply _)
  simp only [HasMatch, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  by_cases ha : 2*a < n
  · by_cases hb : 2*b+1 < n
    · simpa only [ha,hb,true_and] using he a b
    · simp only [hb,and_false,false_and,Set.ofPred_false,MeasurableSet.empty]
  · simp only [ha,false_and,Set.ofPred_false,MeasurableSet.empty]

theorem measurable_colorTerminates : MeasurableSet {ω : Sample α | Terminates ω} := by
  simp only [Terminates, Set.ofPred_exists]
  exact MeasurableSet.iUnion measurable_colorHasMatch

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] in
theorem colorWinner_fiber (c i : α) :
    {ω : Sample α | colorWinner c ω = i} =
      ({ω | ¬ Terminates ω} ∩ {_ω | c = i}) ∪
      ⋃ n : ℕ, ({ω | FirstMatch ω n} ∩ {ω | ω n = i}) := by
  let : Inhabited α := ⟨c⟩
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · intro hi
    by_cases ht : Terminates ω
    · right
      refine ⟨firstLength ω ht - 1, first_at_least ω ht, ?_⟩
      simpa only [colorWinner, dite_eq_left ht] using hi
    · left
      exact ⟨ht, by simpa only [colorWinner, dite_eq_right ht] using hi⟩
  · rintro (⟨ht, hi⟩ | ⟨n, hn, hi⟩)
    · simpa only [colorWinner, dite_eq_right ht] using hi
    · change winner ω = i
      exact (winner_at_first hn).trans hi

theorem measurable_colorWinner (c : α) : Measurable (colorWinner c) := by
  apply measurable_to_countable'
  intro i
  change MeasurableSet {ω : Sample α | colorWinner c ω = i}
  rw [colorWinner_fiber]
  apply MeasurableSet.union
  · exact measurable_colorTerminates.compl.inter (MeasurableSet.const _)
  · apply MeasurableSet.iUnion
    intro n
    exact ((measurable_colorHasMatch (n+1)).inter
      (measurable_colorHasMatch n).compl).inter
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)

theorem colorWinner_nat_eq (c : ℕ) : colorWinner c = sourceWinner c := by
  funext ω
  by_cases ht : Terminates ω
  · simp only [colorWinner, sourceWinner, ite_eq_left ht, winner, dite_eq_left ht]
  · simp only [colorWinner, sourceWinner, ite_eq_right ht, dite_eq_right ht]

/-- Equality of genuine winner pushforward measures, including transported
fallbacks; not an assumed relation between two arbitrary laws. -/
theorem colorWinner_measure_transport (p : PMF α) (c : α)
    (e : α → ℕ) (he : Function.Injective e) :
    ((colorSampleMeasure p).map (colorWinner c)).map e =
      (sampleMeasure (p.map e)).map (sourceWinner (e c)) := by
  have hm : Measurable e := measurable_of_countable _
  rw [Measure.map_map hm (measurable_colorWinner c)]
  rw [← colorSampleMeasure_nat, ← colorSampleMeasure_map p e hm,
    Measure.map_map (measurable_sourceWinner (e c)) (measurable_relabelSample e hm)]
  congr 1
  funext ω
  exact (colorWinner_relabel e he c ω).symm.trans
    (congrFun (colorWinner_nat_eq (e c)) (relabelSample e ω))

end Shoe
