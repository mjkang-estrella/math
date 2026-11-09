import ShoePair

namespace Shoe
open MeasureTheory
open scoped ENNReal

theorem pair_equality_probability (p : DiscreteLaw ℕ) :
    sampleMeasure p {ω | ω 0 = ω 1} = collisionMass p := by
  have he : {ω : Sample ℕ | ω 0 = ω 1} =
      ⋃ i : ℕ, {ω | ω 0 = i ∧ ω 1 = i} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun h => ⟨ω 0,rfl,h.symm⟩, fun ⟨i,hi,hj⟩ => hi.trans hj.symm⟩
  have hd : Pairwise fun i j : ℕ => Disjoint
      {ω : Sample ℕ | ω 0 = i ∧ ω 1 = i} {ω | ω 0 = j ∧ ω 1 = j} := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun ω hi hj => hij (hi.1.symm.trans hj.1))
  have hm (i : ℕ) : MeasurableSet {ω : Sample ℕ | ω 0 = i ∧ ω 1 = i} :=
    (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
      (measurableSet_eq_fun (measurable_pi_apply 1) measurable_const)
  rw [he, measure_iUnion hd hm]
  exact tsum_congr (fun i => two_coordinates_same_color p 0 1 i (by omega))

/-- Conditional equality sampling as normalized restriction, followed by taking
its left color. This is defined from the actual iid experiment. -/
noncomputable def conditionalColorMeasure (p : DiscreteLaw ℕ) : Measure ℕ :=
  (collisionMass p)⁻¹ •
    (((sampleMeasure p).restrict {ω | ω 0 = ω 1}).map (fun ω => ω 0))

theorem conditionalColorMeasure_apply (p : DiscreteLaw ℕ) (i : ℕ) :
    conditionalColorMeasure p {i} = pairLaw p i := by
  unfold conditionalColorMeasure
  rw [Measure.smul_apply, Measure.map_apply (measurable_pi_apply 0)
    (measurableSet_singleton i), Measure.restrict_apply
      ((measurable_pi_apply 0) (measurableSet_singleton i))]
  have he : (fun ω : Sample ℕ => ω 0) ⁻¹' {i} ∩ {ω | ω 0 = ω 1} =
      {ω | ω 0 = i ∧ ω 1 = i} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨hi,h⟩ => ⟨hi,h.symm.trans hi⟩,
      fun ⟨hi,hj⟩ => ⟨hi,hi.trans hj.symm⟩⟩
  rw [he, two_coordinates_same_color p 0 1 i (by omega)]
  exact mul_comm _ _

instance conditionalColorMeasure_probability (p : DiscreteLaw ℕ) :
    IsProbabilityMeasure (conditionalColorMeasure p) := by
  constructor
  unfold conditionalColorMeasure
  rw [Measure.smul_apply, Measure.map_apply (measurable_pi_apply 0) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    pair_equality_probability]
  exact ENNReal.inv_mul_cancel (collisionMass_ne_zero p) (collisionMass_ne_top p)

theorem conditionalColorMeasure_toPMF (p : DiscreteLaw ℕ) :
    (conditionalColorMeasure p).toPMF = pairLaw p := by
  apply PMF.ext
  intro i
  exact conditionalColorMeasure_apply p i

end Shoe
