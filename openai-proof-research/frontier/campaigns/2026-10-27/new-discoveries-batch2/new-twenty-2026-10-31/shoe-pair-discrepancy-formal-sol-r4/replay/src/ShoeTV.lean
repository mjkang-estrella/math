import ShoeMinorization
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Shoe
open scoped ENNReal

theorem pmf_real_summable (p : PMF ℕ) : Summable (fun i => (p i).toReal) := by
  apply ENNReal.summable_toReal
  rw [p.tsum_coe]
  exact ENNReal.one_ne_top

theorem pmf_real_sum (p : PMF ℕ) : ∑' i, (p i).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun i => ne_of_lt
    (lt_of_le_of_lt (p.coe_le_one i) ENNReal.one_lt_top)), p.tsum_coe]
  rfl

noncomputable def countableTV (p q : PMF ℕ) : ℝ :=
  (∑' i, |(p i).toReal - (q i).toReal|)/2

theorem overlap_summable (p q : PMF ℕ) :
    Summable (fun i => min (p i).toReal (q i).toReal) :=
  Summable.of_nonneg_of_le (fun _ => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun _ => min_le_left _ _) (pmf_real_summable p)

theorem tv_absolute_summable (p q : PMF ℕ) :
    Summable (fun i => |(p i).toReal - (q i).toReal|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun i => ?_) ((pmf_real_summable p).add (pmf_real_summable q))
  have hp : 0 ≤ (p i).toReal := ENNReal.toReal_nonneg
  have hq : 0 ≤ (q i).toReal := ENNReal.toReal_nonneg
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem countableTV_overlap (p q : PMF ℕ) :
    countableTV p q = 1 - ∑' i, min (p i).toReal (q i).toReal := by
  have he (i : ℕ) : |(p i).toReal - (q i).toReal| =
      ((p i).toReal + (q i).toReal) - 2*min (p i).toReal (q i).toReal := by
    rcases le_total (p i).toReal (q i).toReal with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  unfold countableTV
  simp_rw [he]
  rw [((pmf_real_summable p).add (pmf_real_summable q)).tsum_sub
      ((overlap_summable p q).mul_left 2),
    (pmf_real_summable p).tsum_add (pmf_real_summable q),
    (overlap_summable p q).tsum_mul_left, pmf_real_sum, pmf_real_sum]
  ring

theorem discrepancy_uniform_bound (p : DiscreteLaw ℕ) :
    countableTV (pairLaw p) (winningLaw p) ≤ 255/256 := by
  rw [countableTV_overlap]
  have hm (i : ℕ) : (pairLaw p i).toReal/256 ≤
      min (pairLaw p i).toReal (winningLaw p i).toReal := by
    apply le_min
    · have hn : 0 ≤ (pairLaw p i).toReal := ENNReal.toReal_nonneg
      linarith
    · exact winningLaw_minorization p i
  have hs := ((pmf_real_summable (pairLaw p)).div_const 256).tsum_le_tsum hm
    (overlap_summable (pairLaw p) (winningLaw p))
  have hdiv := ((pmf_real_summable (pairLaw p)).hasSum.div_const 256).tsum_eq
  rw [hdiv, pmf_real_sum] at hs
  linarith

noncomputable def universalDiscrepancy : ℝ :=
  sSup (Set.range (fun p : DiscreteLaw ℕ => countableTV (pairLaw p) (winningLaw p)))

theorem universalDiscrepancy_le : universalDiscrepancy ≤ 255/256 := by
  apply csSup_le
  · exact ⟨_, ⟨PMF.pure 0,rfl⟩⟩
  · rintro _ ⟨p,rfl⟩
    exact discrepancy_uniform_bound p

theorem universalDiscrepancy_strict : universalDiscrepancy < 1 :=
  lt_of_le_of_lt universalDiscrepancy_le (by norm_num)

end Shoe
