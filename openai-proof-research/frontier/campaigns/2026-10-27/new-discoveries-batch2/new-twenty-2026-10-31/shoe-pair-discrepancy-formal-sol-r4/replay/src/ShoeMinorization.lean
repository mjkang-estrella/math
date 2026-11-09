import ShoeScale
import Mathlib.Tactic.Finiteness

namespace Shoe
open MeasureTheory
open scoped ENNReal

theorem real_goodBlock_lower (p : DiscreteLaw ℕ) (hs : realMass p < 1/64)
    {a b i : ℕ} (ha : a < blockSize p) (hb : b < blockSize p) :
    (realProb p i)^2/4 ≤
      (sampleMeasure p {ω | GoodBlock ω (blockSize p) a b i}).toReal := by
  let K := blockSize p
  let t := realProb p i
  have ht : 0 ≤ t := realProb_nonneg p i
  have ht1 : t ≤ 1 := realProb_le_one p i
  obtain ⟨hk2,_,hk,hks,_⟩ := blockSize_scale p hs
  have hkt : (K : ℝ)*t ≤ 1/4 :=
    (mul_le_mul_of_nonneg_left (realProb_le_sqrt p i) (Nat.cast_nonneg K)).trans hk
  have he : ((2*K-2 : ℕ) : ℝ) ≤ 2*(K : ℝ) := by
    exact_mod_cast (Nat.sub_le (2*K) 2)
  have hpow := bernoulli_complement t ht ht1 (2*K-2)
  have hpow2 : (1-t)^(2*K-2) ≥ 1/2 := by
    have hm := mul_le_mul_of_nonneg_right he ht
    linarith
  have hi := congrArg ENNReal.toReal (isolated_probability p ha hb (i := i))
  have hsub : (1-p i).toReal = 1-t := by
    simpa [t,realProb] using ENNReal.toReal_sub_of_le (p.coe_le_one i) ENNReal.one_ne_top
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, hsub] at hi
  have hlo := mul_le_mul_of_nonneg_left hpow2 (sq_nonneg t)
  have hpi : p i ≠ ∞ := ne_of_lt (lt_of_le_of_lt (p.coe_le_one i) ENNReal.one_lt_top)
  have hsm := collisionMass_ne_top p
  have hu := isolated_le_good_add_collisions p K a b i
  have hr := ENNReal.toReal_mono (by finiteness) hu
  rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness)] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hr
  change (sampleMeasure p {ω | Isolated ω K a b i}).toReal ≤
    (sampleMeasure p {ω | GoodBlock ω K a b i}).toReal +
      (K : ℝ)*K*(t*t*realMass p) at hr
  have hbad : (K : ℝ)*K*(t*t*realMass p) ≤ t^2/16 := by
    have hm := mul_le_mul_of_nonneg_right hks (sq_nonneg t)
    nlinarith
  change (sampleMeasure p {ω | Isolated ω K a b i}).toReal =
    t*t*(1-t)^(2*K-2) at hi
  nlinarith


theorem real_pairLaw (p : DiscreteLaw ℕ) (i : ℕ) :
    (pairLaw p i).toReal = (realProb p i)^2 / realMass p := by
  change (p i * p i * (collisionMass p)⁻¹).toReal = _
  simp only [realProb, realMass, ENNReal.toReal_mul, ENNReal.toReal_inv,
    div_eq_mul_inv, pow_two]

theorem small_winning_lower (p : DiscreteLaw ℕ) (hs : realMass p < 1/64) (i : ℕ) :
    (blockSize p : ℝ)^2 * (realProb p i)^2 / 4 ≤ (winningLaw p i).toReal := by
  let s := (Finset.range (blockSize p)).product (Finset.range (blockSize p))
  have hf : winningLaw p i ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt ((winningLaw p).coe_le_one i) ENNReal.one_lt_top)
  have hsum := ENNReal.toReal_mono hf (goodBlock_sum_le_winning p (blockSize p) i)
  rw [ENNReal.toReal_sum (fun ab _ => measure_ne_top _ _)] at hsum
  calc
    _ = ∑ _ab ∈ s, (realProb p i)^2/4 := by
      simp [s, Finset.card_product, nsmul_eq_mul, pow_two]
      ring
    _ ≤ ∑ ab ∈ s,
        (sampleMeasure p {ω | GoodBlock ω (blockSize p) ab.1 ab.2 i}).toReal := by
      apply Finset.sum_le_sum
      intro ab hab
      have hm := Finset.mem_product.mp hab
      exact real_goodBlock_lower p hs (Finset.mem_range.mp hm.1) (Finset.mem_range.mp hm.2)
    _ ≤ _ := hsum

/-- All branches, including zeros and point masses, for the actual two derived laws. -/
theorem winningLaw_minorization (p : DiscreteLaw ℕ) (i : ℕ) :
    (pairLaw p i).toReal / 256 ≤ (winningLaw p i).toReal := by
  rw [real_pairLaw]
  have hspos := realMass_pos p
  have ht : 0 ≤ (realProb p i)^2 := sq_nonneg _
  by_cases hs : realMass p < 1/64
  · have hy := small_winning_lower p hs i
    have hk := (blockSize_scale p hs).2.2.2.2
    have hm := mul_le_mul_of_nonneg_right hk ht
    have he : (realProb p i)^2 / realMass p /256 =
        (1/(64*realMass p))*(realProb p i)^2/4 := by ring
    rw [he]
    linarith
  · have hsf : 1/64 ≤ realMass p := le_of_not_gt hs
    have hf : winningLaw p i ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt ((winningLaw p).coe_le_one i) ENNReal.one_lt_top)
    have hy := ENNReal.toReal_mono hf (winningLaw_first_pair_lower p i)
    simp only [ENNReal.toReal_mul] at hy
    change realProb p i * realProb p i ≤ (winningLaw p i).toReal at hy
    have hb : (realProb p i)^2 / realMass p /256 ≤ (realProb p i)^2 := by
      apply (div_le_iff₀ (by norm_num : (0:ℝ)<256)).2
      apply (div_le_iff₀ hspos).2
      nlinarith [mul_nonneg ht (show 0 ≤ realMass p-1/64 by linarith)]
    nlinarith

end Shoe
