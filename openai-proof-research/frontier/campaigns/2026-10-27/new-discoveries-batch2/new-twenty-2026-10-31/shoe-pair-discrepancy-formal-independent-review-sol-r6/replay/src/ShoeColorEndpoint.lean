import ShoeColorConditional

namespace Shoe
open MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def colorTV {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) : ℝ :=
  sSup (Set.range (fun A : Set α => |(μ A).toReal - (ν A).toReal|))

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

theorem colorTV_coding (μ ν : Measure α) (e : α → ℕ)
    (he : Function.Injective e) : colorTV μ ν = colorTV (μ.map e) (ν.map e) := by
  have hm : Measurable e := measurable_of_countable _
  unfold colorTV
  congr 1
  ext x
  constructor
  · rintro ⟨A,rfl⟩
    refine ⟨e '' A, ?_⟩
    dsimp only
    rw [Measure.map_apply hm (Set.to_countable _).measurableSet,
      Measure.map_apply hm (Set.to_countable _).measurableSet,
      Set.preimage_image_eq _ he]
  · rintro ⟨B,rfl⟩
    refine ⟨e ⁻¹' B, ?_⟩
    dsimp only
    rw [Measure.map_apply hm (Set.to_countable _).measurableSet,
      Measure.map_apply hm (Set.to_countable _).measurableSet]

noncomputable def colorDiscrepancy (p : PMF α) (c : α) : ℝ :=
  colorTV (colorConditionalMeasure p) ((colorSampleMeasure p).map (colorWinner c))

theorem colorDiscrepancy_coding (p : PMF α) (c : α)
    (e : α → ℕ) (he : Function.Injective e) :
    colorDiscrepancy p c = sourceDiscrepancy (p.map e) (e c) := by
  unfold colorDiscrepancy
  rw [colorTV_coding _ _ e he, colorConditionalMeasure_transport p e he,
    colorWinner_measure_transport p c e he]
  unfold sourceDiscrepancy sourceTV sourceX sourceY colorTV
  simp only [Measure.toPMF_toMeasure]

/-- Every countable color law, including zeros, finite support and point masses.
The proof uses semantic transport of both experiments and TV, then consumes
the existing Nat bound rather than reproving its elementary inequality. -/
theorem countable_color_discrepancy_bound (p : PMF α) (c : α) :
    colorDiscrepancy p c ≤ 255/256 := by
  obtain ⟨e,he⟩ := exists_injective_nat α
  rw [colorDiscrepancy_coding p c e he]
  exact sourceDiscrepancy_bound (p.map e) (e c)

theorem countable_color_strict_universal_supremum (c : α) :
    sSup (Set.range (fun p : PMF α => colorDiscrepancy p c)) ≤ 255/256 ∧
    sSup (Set.range (fun p : PMF α => colorDiscrepancy p c)) < 1 := by
  have h : sSup (Set.range (fun p : PMF α => colorDiscrepancy p c)) ≤ 255/256 := by
    apply csSup_le
    · exact ⟨_,⟨PMF.pure c,rfl⟩⟩
    · rintro _ ⟨p,rfl⟩
      exact countable_color_discrepancy_bound p c
  exact ⟨h,lt_of_le_of_lt h (by norm_num)⟩

theorem finite_zeroExtension_discrepancy (n : ℕ) (p : PMF (Fin n)) (c : Fin n) :
    colorDiscrepancy p c = sourceDiscrepancy (p.map Fin.val) c.val :=
  colorDiscrepancy_coding p c Fin.val Fin.val_injective

end Shoe
