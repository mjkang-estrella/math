import ShoeBlock

namespace Shoe
open MeasureTheory
open scoped ENNReal

noncomputable def collisionMass (p : DiscreteLaw ℕ) : ℝ≥0∞ := ∑' i, p i * p i

theorem collisionMass_le_one (p : DiscreteLaw ℕ) : collisionMass p ≤ 1 := by
  rw [← p.tsum_coe]
  apply ENNReal.tsum_le_tsum
  intro i
  calc p i * p i ≤ p i * 1 := mul_le_mul le_rfl (p.coe_le_one i) bot_le bot_le
       _ = p i := mul_one _

theorem collisionMass_ne_zero (p : DiscreteLaw ℕ) : collisionMass p ≠ 0 := by
  obtain ⟨i,hi⟩ := p.support_nonempty
  have hp : 0 < p i := (p.apply_pos_iff i).2 hi
  have hpp : 0 < p i * p i := pos_iff_ne_zero.mpr (mul_ne_zero hp.ne' hp.ne')
  exact ne_of_gt (lt_of_lt_of_le hpp (ENNReal.le_tsum (f := fun j => p j * p j) i))

theorem collisionMass_ne_top (p : DiscreteLaw ℕ) : collisionMass p ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (collisionMass_le_one p) ENNReal.one_lt_top)

/-- The normalized independent-pair equality masses, not an assumed minorization. -/
noncomputable def pairLaw (p : DiscreteLaw ℕ) : PMF ℕ :=
  ⟨fun i => p i * p i * (collisionMass p)⁻¹, by
    apply ENNReal.summable.hasSum_iff.2
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_inv_cancel (collisionMass_ne_zero p) (collisionMass_ne_top p)⟩

theorem two_coordinates_same_color (p : DiscreteLaw ℕ) (a b i : ℕ) (hab : a ≠ b) :
    sampleMeasure p {ω | ω a = i ∧ ω b = i} = p i * p i := by
  have hs : {ω : Sample ℕ | ω a = i ∧ ω b = i} =
      Set.pi (({a,b} : Finset ℕ) : Set ℕ) (fun _ => ({i} : Set ℕ)) := by
    ext ω
    simp
  rw [hs, cylinder_probability p {a,b} (fun _ => {i}) (by intros; exact measurableSet_singleton _)]
  simp [hab, pow_two, p.toMeasure_apply_singleton i (measurableSet_singleton i)]

/-- The real first-pair event gives an unconditional lower bound on the true law. -/
theorem winningLaw_first_pair_lower (p : DiscreteLaw ℕ) (i : ℕ) :
    p i * p i ≤ winningLaw p i := by
  rw [winningLaw_apply, ← two_coordinates_same_color p 0 1 i (by omega)]
  apply measure_mono
  intro ω hω
  exact (winner_first_pair (hω.1.trans hω.2.symm)).trans hω.1

end Shoe
