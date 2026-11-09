import ShoeDiagonal
import Mathlib.Analysis.SpecificLimits.Basic

namespace Shoe
open MeasureTheory Filter
open scoped ENNReal Topology
attribute [local instance] Classical.propDecidable

theorem nontermination_probability_zero (p : DiscreteLaw ℕ) :
    sampleMeasure p {ω | ¬ Terminates ω} = 0 := by
  have hr : 1 - collisionMass p < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (collisionMass_ne_zero p)
  have hlim := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro N
  apply le_trans _ (stopping_tail_bound p N)
  apply measure_mono
  intro ω hω hm
  exact hω ⟨2*N,hm⟩

theorem ae_terminates (p : DiscreteLaw ℕ) : ∀ᵐ ω ∂sampleMeasure p, Terminates ω := by
  rw [ae_iff]
  exact nontermination_probability_zero p

/-- Choosing any other color on the exceptional nontermination set has no
 effect on the random-variable law. -/
theorem fallback_ae (p : DiscreteLaw ℕ) (c : ℕ) :
    (fun ω => if Terminates ω then winner ω else c) =ᵐ[sampleMeasure p] winner := by
  classical
  filter_upwards [ae_terminates p] with ω hω
  exact ite_eq_left hω

end Shoe
