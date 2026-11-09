import Zeros
import EvaluationCertificates
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace BesselFejer

lemma rpow_two_fifths_pow_five (x : ℝ) (hx : 0 ≤ x) :
    (x^(2/5 : ℝ))^5 = x^2 := by
  calc
    (x^(2/5 : ℝ))^5 = (x^(2/5 : ℝ))^(5 : ℝ) := (Real.rpow_natCast _ 5).symm
    _ = x^((2/5 : ℝ)*5) := (Real.rpow_mul hx _ _).symm
    _ = x^2 := by norm_num

lemma rpow_two_fifths_bounds (x l u c d : ℝ) (hl : 0 ≤ l)
    (hxl : l ≤ x) (hxu : x ≤ u) (hd : 0 ≤ d)
    (hc5 : c^5 ≤ l^2) (hd5 : u^2 ≤ d^5) :
    c ≤ x^(2/5 : ℝ) ∧ x^(2/5 : ℝ) ≤ d := by
  have hx : 0 ≤ x := le_trans hl hxl
  have hR : 0 ≤ x^(2/5 : ℝ) := Real.rpow_nonneg hx _
  have hpow := rpow_two_fifths_pow_five x hx
  constructor
  · apply le_of_pow_le_pow_left₀ (by decide : 5 ≠ 0) hR
    rw [hpow]
    exact hc5.trans (pow_le_pow_left₀ hl hxl 2)
  · apply le_of_pow_le_pow_left₀ (by decide : 5 ≠ 0) hd
    rw [hpow]
    exact (pow_le_pow_left₀ hx hxu 2).trans hd5

lemma scaled_q_bounds (x l u : ℝ) (hl : 0 ≤ l) (hxl : l ≤ x) (hxu : x ≤ u) :
    (l*(47/50 : ℝ))^2/4 ≤ (x*(47/50 : ℝ))^2/4 ∧
    (x*(47/50 : ℝ))^2/4 ≤ (u*(47/50 : ℝ))^2/4 := by
  have hcx : 0 ≤ x*(47/50 : ℝ) := mul_nonneg (le_trans hl hxl) (by norm_num)
  have hcl : 0 ≤ l*(47/50 : ℝ) := mul_nonneg hl (by norm_num)
  have hle := pow_le_pow_left₀ hcl (mul_le_mul_of_nonneg_right hxl (by norm_num : (0 : ℝ) ≤ 47/50)) 2
  have hue := pow_le_pow_left₀ hcx (mul_le_mul_of_nonneg_right hxu (by norm_num : (0 : ℝ) ≤ 47/50)) 2
  constructor <;> linarith

lemma scaled_J0_first_upper (a : ℝ)
    (ha : a ∈ Set.Icc (24048/10000 : ℝ) (24049/10000)) :
    besselJ0 (a*(47/50 : ℝ)) ≤ 7703/100000 := by
  have hs := scaled_q_bounds a (24048/10000) (24049/10000) (by norm_num) ha.1 ha.2
  have hp := evalA_bound ((a*(47/50 : ℝ))^2/4) (by nlinarith [hs.1]) (by nlinarith [hs.2])
  have hq : |(a*(47/50 : ℝ))^2/4| ≤ 9 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [hs.2]
  have he := (abs_le.mp (series_error _ hq)).2
  have ht : 2*(9 : ℝ)^20 / ((20 : ℕ).factorial : ℝ)^2 < 1/200000 := by norm_num
  change series ((a*(47/50 : ℝ))^2/4) ≤ 7703/100000
  linarith

lemma scaled_J0_second_upper (b : ℝ)
    (hb : b ∈ Set.Icc (55200/10000 : ℝ) (55201/10000)) :
    besselJ0 (b*(47/50 : ℝ)) ≤ -569/5000 := by
  have hs := scaled_q_bounds b (55200/10000) (55201/10000) (by norm_num) hb.1 hb.2
  have hp := evalB_bound ((b*(47/50 : ℝ))^2/4) (by nlinarith [hs.1]) (by nlinarith [hs.2])
  have hq : |(b*(47/50 : ℝ))^2/4| ≤ 9 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [hs.2]
  have he := (abs_le.mp (series_error _ hq)).2
  have ht : 2*(9 : ℝ)^20 / ((20 : ℕ).factorial : ℝ)^2 < 1/100000 := by norm_num
  change series ((b*(47/50 : ℝ))^2/4) ≤ -569/5000
  linarith

lemma source_kernel_interior_negative :
    sourceKernel (2/5) 2 (47/50) < -(1/500 : ℝ) := by
  let a := sourceZero 1
  let b := sourceZero 2
  have ha : a ∈ Set.Icc (24048/10000 : ℝ) (24049/10000) := source_first_two_zero_bounds.1
  have hb : b ∈ Set.Icc (55200/10000 : ℝ) (55201/10000) := source_first_two_zero_bounds.2
  have hA := rpow_two_fifths_bounds a (24048/10000) (24049/10000)
    (14204/10000) (14205/10000) (by norm_num) ha.1 ha.2 (by norm_num)
    (by norm_num) (by norm_num)
  have hB := rpow_two_fifths_bounds b (55200/10000) (55201/10000)
    (19805/10000) (19806/10000) (by norm_num) hb.1 hb.2 (by norm_num)
    (by norm_num) (by norm_num)
  have hJA := scaled_J0_first_upper a ha
  have hJB := scaled_J0_second_upper b hb
  have hRA : 0 ≤ a^(2/5 : ℝ) := Real.rpow_nonneg (by linarith [ha.1]) _
  have hRB : 0 ≤ b^(2/5 : ℝ) := Real.rpow_nonneg (by linarith [hb.1]) _
  have hAb : a^(2/5 : ℝ)*besselJ0 (a*(47/50)) ≤ (14205/10000 : ℝ)*(7703/100000) := by
    calc
      _ ≤ a^(2/5 : ℝ)*(7703/100000) := mul_le_mul_of_nonneg_left hJA hRA
      _ ≤ _ := mul_le_mul_of_nonneg_right hA.2 (by norm_num)
  have hBb : b^(2/5 : ℝ)*besselJ0 (b*(47/50)) ≤ (19805/10000 : ℝ)*(-569/5000) := by
    calc
      _ ≤ b^(2/5 : ℝ)*(-569/5000) := mul_le_mul_of_nonneg_left hJB hRB
      _ ≤ _ := mul_le_mul_of_nonpos_right hB.1 (by norm_num)
  have hk : sourceKernel (2/5) 2 (47/50) =
      (2/3 : ℝ)*a^(2/5 : ℝ)*besselJ0 (a*(47/50)) +
      (1/3 : ℝ)*b^(2/5 : ℝ)*besselJ0 (b*(47/50)) := by
    norm_num [sourceKernel, Finset.sum_range_succ, a, b]
  rw [hk]
  nlinarith

theorem source_counterexample_365454 : ¬SourceClaim365454 := by
  intro h
  have hh := h (2/5) (by norm_num) (by norm_num) 2 (by decide)
    (47/50) (by norm_num) (by norm_num)
  linarith [source_kernel_interior_negative]

end BesselFejer
