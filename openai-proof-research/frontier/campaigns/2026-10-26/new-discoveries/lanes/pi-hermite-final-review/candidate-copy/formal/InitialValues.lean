import Energy
import WallisBounds

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

open Polynomial

theorem sourceCoefficient_pos (n : ℕ) : 0 < sourceCoefficient n := by
  unfold sourceCoefficient
  exact div_pos (mul_pos (by positivity)
    (Real.Gamma_pos_of_pos (by positivity))) (Real.sqrt_pos.mpr Real.pi_pos)

theorem sourceCoefficient_zero : sourceCoefficient 0 = 1 := by
  norm_num [sourceCoefficient, Real.Gamma_one_half_eq, Real.sqrt_ne_zero'.mpr Real.pi_pos]

theorem sourceCoefficient_one : sourceCoefficient 1 = 2 / Real.sqrt Real.pi := by
  norm_num [sourceCoefficient]

theorem sourceCoefficient_add_two (n : ℕ) :
    sourceCoefficient (n + 2) = 2 * ((n : ℝ) + 1) * sourceCoefficient n := by
  unfold sourceCoefficient
  rw [show (((n + 2 : ℕ) : ℝ) + 1) / 2 = ((n : ℝ) + 1) / 2 + 1 by push_cast; ring]
  rw [Real.Gamma_add_one (by positivity : ((n : ℝ) + 1) / 2 ≠ 0), pow_add]
  norm_num
  ring

theorem hermitePoly_recurrence (n : ℕ) :
    hermitePoly (n + 2) = C 2 * X * hermitePoly (n + 1) -
      C (2 * ((n : ℝ) + 1)) * hermitePoly n := by
  rw [show n + 2 = (n + 1) + 1 by omega, hermitePoly, hermitePoly_derivative_succ]

theorem hermiteValue_zero_even (m : ℕ) :
    hermiteValue (2 * m) 0 = (-1 : ℝ) ^ m * sourceCoefficient (2 * m) := by
  induction m with
  | zero => simp [hermiteValue, hermitePoly, sourceCoefficient_zero]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by omega]
    have h := congrArg (fun p : Polynomial ℝ => p.eval 0) (hermitePoly_recurrence (2 * m))
    simp only [eval_sub, eval_mul, eval_C, eval_X, mul_zero, zero_mul, zero_sub] at h
    change (hermitePoly (2 * m + 2)).eval 0 = _
    rw [h, show (hermitePoly (2 * m)).eval 0 =
      (-1 : ℝ) ^ m * sourceCoefficient (2 * m) from ih,
      sourceCoefficient_add_two, pow_succ]
    push_cast
    ring

theorem hermiteValue_zero_odd (m : ℕ) : hermiteValue (2 * m + 1) 0 = 0 := by
  induction m with
  | zero => simp [hermiteValue, hermitePoly]
  | succ m ih =>
    have h := congrArg (fun p : Polynomial ℝ => p.eval 0)
      (hermitePoly_recurrence (2 * m + 1))
    simp only [eval_sub, eval_mul, eval_C, eval_X, mul_zero, zero_mul, zero_sub] at h
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega]
    change (hermitePoly ((2 * m + 1) + 2)).eval 0 = 0
    rw [h, show (hermitePoly (2 * m + 1)).eval 0 = 0 from ih]
    ring

theorem weightedHermite_zero_even (m : ℕ) :
    weightedHermite (2 * m) 0 = (-1 : ℝ) ^ m * sourceCoefficient (2 * m) := by
  simpa [weightedHermite] using hermiteValue_zero_even m

theorem weightedHermite_zero_odd (m : ℕ) : weightedHermite (2 * m + 1) 0 = 0 := by
  simp [weightedHermite, hermiteValue_zero_odd]

theorem weightedSlope_zero_even (m : ℕ) : weightedSlope (2 * m) 0 = 0 := by
  cases m with
  | zero => simp [weightedSlope, hermitePoly]
  | succ m =>
    unfold weightedSlope
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, hermitePoly_derivative_succ]
    simp only [eval_sub, eval_mul, eval_X, eval_C, zero_mul, sub_zero,
      show (hermitePoly (2 * m + 1)).eval 0 = 0 from hermiteValue_zero_odd m]
    ring

def oddSlopeMagnitude (m : ℕ) : ℝ :=
  2 * (2 * (m : ℝ) + 1) * sourceCoefficient (2 * m)

theorem oddSlopeMagnitude_pos (m : ℕ) : 0 < oddSlopeMagnitude m := by
  unfold oddSlopeMagnitude
  exact mul_pos (by positivity) (sourceCoefficient_pos _)

theorem weightedSlope_zero_odd (m : ℕ) :
    weightedSlope (2 * m + 1) 0 = (-1 : ℝ) ^ m * oddSlopeMagnitude m := by
  unfold weightedSlope
  rw [hermitePoly_derivative_succ]
  simp only [eval_sub, eval_mul, eval_X, eval_C, zero_mul, sub_zero,
    show (hermitePoly (2 * m)).eval 0 = (-1 : ℝ) ^ m * sourceCoefficient (2 * m)
      from hermiteValue_zero_even m]
  norm_num
  unfold oddSlopeMagnitude
  ring

theorem initial_energy_even (m : ℕ) :
    energy (2 * m) 0 = (2 * ((2 * m : ℕ) : ℝ) + 1) * sourceCoefficient (2 * m) ^ 2 := by
  rw [energy, weightedHermite_zero_even, weightedSlope_zero_even]
  have hs : ((-1 : ℝ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm m 2, pow_mul]; simp
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, mul_pow, hs, one_mul, add_zero]

theorem source_bulk_even (m : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hq : x ^ 2 < 2 * ((2 * m : ℕ) : ℝ) + 1) :
    |weightedHermite (2 * m) x| ≤ sourceCoefficient (2 * m) * sourceEnvelope (2 * m) x := by
  have h := weighted_bulk_of_initial_energy (2 * m) (sourceCoefficient (2 * m))
    (sourceCoefficient_pos _).le (initial_energy_even m).le x hx hq
  simpa only [sourceEnvelope, div_eq_mul_inv] using h

theorem oddSlopeMagnitude_succ (m : ℕ) :
    oddSlopeMagnitude (m + 1) = 2 * (2 * (m : ℝ) + 3) * oddSlopeMagnitude m := by
  unfold oddSlopeMagnitude
  rw [show 2 * (m + 1) = 2 * m + 2 by omega, sourceCoefficient_add_two]
  push_cast
  ring

theorem odd_initial_energy_ratio (m : ℕ) :
    oddSlopeMagnitude m ^ 2 = (4 * (m : ℝ) + 3) *
      sourceCoefficient (2 * m + 1) ^ 2 * oddEnergyRatio m := by
  induction m with
  | zero =>
    norm_num [oddSlopeMagnitude, sourceCoefficient_zero, sourceCoefficient_one,
      oddEnergyRatio, Real.Wallis.W]
    field_simp
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  | succ m ih =>
    have hc : sourceCoefficient (2 * (m + 1) + 1) =
        4 * ((m : ℝ) + 1) * sourceCoefficient (2 * m + 1) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, sourceCoefficient_add_two]
      push_cast
      ring
    calc
      _ = 4 * (2 * (m : ℝ) + 3) ^ 2 * oddSlopeMagnitude m ^ 2 := by
        rw [oddSlopeMagnitude_succ]; ring
      _ = 4 * (2 * (m : ℝ) + 3) ^ 2 * ((4 * (m : ℝ) + 3) *
          sourceCoefficient (2 * m + 1) ^ 2 * oddEnergyRatio m) := by rw [ih]
      _ = _ := by
        rw [hc, oddEnergyRatio_succ]
        push_cast
        field_simp
        ring

theorem odd_initial_corrected_bound (m : ℕ) :
    oddSlopeMagnitude m ^ 2 * (1 - 1 / (2 * (4 * (m : ℝ) + 3) ^ 2)) <
      (4 * (m : ℝ) + 3) * sourceCoefficient (2 * m + 1) ^ 2 := by
  have h := mul_lt_mul_of_pos_left (correctedOddRatio_lt_one m)
    (show 0 < (4 * (m : ℝ) + 3) * sourceCoefficient (2 * m + 1) ^ 2 from
      mul_pos (by positivity) (sq_pos_of_pos (sourceCoefficient_pos _)))
  rw [odd_initial_energy_ratio]
  simpa only [correctedOddRatio, mul_assoc, mul_one] using h

theorem odd_initial_small_bound (m : ℕ) (hm : 1 ≤ m) :
    oddSlopeMagnitude m ^ 2 ≤ (99 / 98 : ℝ) *
      ((4 * (m : ℝ) + 3) * sourceCoefficient (2 * m + 1) ^ 2) := by
  have hg : oddEnergyRatio m ≤ (99 / 98 : ℝ) := by
    have h := oddEnergyRatio_le_nine_pi m hm
    nlinarith [Real.pi_lt_d4]
  rw [odd_initial_energy_ratio]
  have hp : 0 ≤ (4 * (m : ℝ) + 3) * sourceCoefficient (2 * m + 1) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hg hp]

end HermiteEnvelope
