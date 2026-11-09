import SquaredAverage

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Filter

namespace MittagModulus

noncomputable def halfBetaMoment (n : ℕ) : ℝ := ∫ u in (0 : ℝ)..1, (1 - u ^ 2) ^ n

theorem halfBetaMoment_zero : halfBetaMoment 0 = 1 := by
  simp [halfBetaMoment]

theorem halfBetaMoment_succ (n : ℕ) :
    halfBetaMoment (n + 1) = (2 * (n + 1 : ℝ)) / (2 * (n : ℝ) + 3) * halfBetaMoment n := by
  have hd (u : ℝ) : HasDerivAt (fun y : ℝ => y * (1 - y ^ 2) ^ (n + 1))
      ((1 - u ^ 2) ^ (n + 1) - 2 * (n + 1 : ℝ) * u ^ 2 * (1 - u ^ 2) ^ n) u := by
    convert (hasDerivAt_id u).mul
      (((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)).pow (n + 1)) using 1 <;>
      (try funext y) <;> norm_num
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun u _ => hd u)
    (by apply Continuous.intervalIntegrable; fun_prop)
  have he : (fun u : ℝ => (1 - u ^ 2) ^ (n + 1) -
      2 * (n + 1 : ℝ) * u ^ 2 * (1 - u ^ 2) ^ n) =
      (fun u : ℝ => (2 * (n : ℝ) + 3) * (1 - u ^ 2) ^ (n + 1) -
        2 * (n + 1 : ℝ) * (1 - u ^ 2) ^ n) := by
    funext u
    rw [pow_succ]
    ring
  rw [he] at hi
  rw [intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  simp only [one_pow, sub_self, zero_pow (by omega : n + 1 ≠ 0), mul_zero,
    zero_pow (by norm_num : 2 ≠ 0), sub_zero, zero_mul] at hi
  change (2 * (n : ℝ) + 3) * halfBetaMoment (n + 1) -
    2 * (n + 1 : ℝ) * halfBetaMoment n = 0 at hi
  have hden : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  nlinarith

theorem Gamma_three_halves : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  have h := Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)
  rw [Real.Gamma_one_half_eq] at h
  norm_num at h ⊢
  linarith

theorem halfBetaMoment_eq_gamma (n : ℕ) :
    halfBetaMoment n = Real.sqrt Real.pi * (n.factorial : ℝ) /
      (2 * Real.Gamma ((n : ℝ) + 3 / 2)) := by
  induction n with
  | zero =>
    rw [halfBetaMoment_zero]
    simp only [Nat.cast_zero, Nat.factorial_zero, Nat.cast_one, zero_add, Gamma_three_halves]
    have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    field_simp
  | succ n ih =>
    rw [halfBetaMoment_succ, ih, Nat.factorial_succ]
    push_cast
    rw [show (n : ℝ) + 1 + 3 / 2 = ((n : ℝ) + 3 / 2) + 1 by ring,
      Real.Gamma_add_one (by positivity : (n : ℝ) + 3 / 2 ≠ 0)]
    field_simp

theorem hasSum_mittagReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / Real.Gamma (a * (n : ℝ) + b))
      (mittagReal a b x) := by
  have h := Complex.hasSum_re (hasSum_mittagLeffler ha hb (x : ℂ))
  rw [mittagLeffler_ofReal] at h
  simpa only [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re] using h

theorem mittag_one_eq_exp (z : ℂ) : mittagLeffler 1 1 z = Complex.exp z := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  unfold mittagLeffler
  apply tsum_congr
  intro n
  simp only [one_mul, Real.Gamma_nat_eq_factorial, Complex.ofReal_natCast]

theorem exp_series_real (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

theorem halfExp_partial_bound (x : ℝ) (N : ℕ) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    ‖∑ n ∈ Finset.range N, (-x * (1 - u ^ 2)) ^ n / (n.factorial : ℝ)‖ ≤ Real.exp |x| := by
  have hU : 0 ≤ 1 - u ^ 2 := by nlinarith [mul_self_le_mul_self hu.1 hu.2]
  have hU1 : 1 - u ^ 2 ≤ 1 := by nlinarith [sq_nonneg u]
  have hterm (n : ℕ) : ‖(-x * (1 - u ^ 2)) ^ n / (n.factorial : ℝ)‖ ≤
      |x| ^ n / (n.factorial : ℝ) := by
    rw [norm_div, norm_pow, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg hU, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (n.factorial : ℝ))]
    gcongr
    exact mul_le_of_le_one_right (abs_nonneg x) hU1
  calc
    ‖∑ n ∈ Finset.range N, (-x * (1 - u ^ 2)) ^ n / (n.factorial : ℝ)‖ ≤
        ∑ n ∈ Finset.range N, ‖(-x * (1 - u ^ 2)) ^ n / (n.factorial : ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, |x| ^ n / (n.factorial : ℝ) :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ ≤ Real.exp |x| := by
      simpa only [(exp_series_real |x|).tsum_eq] using
        (exp_series_real |x|).summable.sum_le_tsum (Finset.range N) (fun _ _ => by positivity)

theorem integral_halfExp_term (x : ℝ) (n : ℕ) :
    (∫ u in (0 : ℝ)..1, (-x * (1 - u ^ 2)) ^ n / (n.factorial : ℝ)) =
      (Real.sqrt Real.pi / 2) * ((-x) ^ n / Real.Gamma ((n : ℝ) + 3 / 2)) := by
  have he : (fun u : ℝ => (-x * (1 - u ^ 2)) ^ n / (n.factorial : ℝ)) =
      (fun u : ℝ => ((-x) ^ n / (n.factorial : ℝ)) * (1 - u ^ 2) ^ n) := by
    funext u
    rw [mul_pow]
    ring
  rw [he, intervalIntegral.integral_const_mul]
  change (-x) ^ n / (n.factorial : ℝ) * halfBetaMoment n = _
  rw [halfBetaMoment_eq_gamma]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem integral_halfExp_eq_mittagReal (x : ℝ) :
    (∫ u in (0 : ℝ)..1, Real.exp (-x * (1 - u ^ 2))) =
      (Real.sqrt Real.pi / 2) * mittagReal 1 (3 / 2) (-x) := by
  have hlim := betaAverage_tendsto (β := (0 : ℝ)) (C := (1 : ℝ))
    (M := Real.exp |x|) (x := (1 : ℝ)) 0
    (F := fun N u => ∑ n ∈ Finset.range N, (-x * (1 - u ^ 2)) ^ n / (n.factorial : ℝ))
    (f := fun u => Real.exp (-x * (1 - u ^ 2)))
    (fun _ => by fun_prop) (fun N u hu => halfExp_partial_bound x N hu)
    (fun u _ => (exp_series_real (-x * (1 - u ^ 2))).summable.hasSum_iff_tendsto_nat.mp
      (exp_series_real (-x * (1 - u ^ 2)))) ⟨zero_le_one, le_rfl⟩
  simp only [betaAverage, zero_smul, sub_zero, Nat.cast_zero,
    zero_add, one_mul, one_smul, pow_zero] at hlim
  have he (N : ℕ) :
      (∫ u in (0 : ℝ)..1, ∑ n ∈ Finset.range N,
        (-x * (1 - u ^ 2)) ^ n / (n.factorial : ℝ)) =
      ∑ n ∈ Finset.range N, (Real.sqrt Real.pi / 2) *
        ((-x) ^ n / Real.Gamma ((n : ℝ) + 3 / 2)) := by
    rw [intervalIntegral.integral_finsetSum (fun _ _ => by
      apply Continuous.intervalIntegrable; fun_prop)]
    simp only [integral_halfExp_term]
  simp_rw [he] at hlim
  have hs := (hasSum_mittagReal zero_lt_one (by norm_num : (0 : ℝ) < 3 / 2) (-x)).mul_left
    (Real.sqrt Real.pi / 2)
  simp only [one_mul] at hs
  exact (tendsto_nhds_unique hlim (hs.summable.hasSum_iff_tendsto_nat.mp hs))

end MittagModulus
