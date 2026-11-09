import Mathlib

namespace CStarSendov

open scoped ComplexOrder

noncomputable def phase (t : ℝ) : ℂ := Complex.exp ((t * Real.pi : ℝ) * Complex.I)
noncomputable def sqrtArg (t : ℝ) : ℂ := 1 + (16/27:ℂ) * (star (phase t))^2
noncomputable def branch (t : ℝ) : ℂ :=
  ((3 * Real.sqrt 3 / 4 : ℝ) : ℂ) * phase t * Complex.sqrt (sqrtArg t)
noncomputable def criticalPlus (t : ℝ) : ℂ := (3/10:ℂ) * (1 + branch t)
noncomputable def criticalMinus (t : ℝ) : ℂ := (3/10:ℂ) * (1 - branch t)
noncomputable def rootOne (_ : ℝ) : ℂ := 9/10
noncomputable def rootPlus (t : ℝ) : ℂ := (27/40:ℂ) * phase t
noncomputable def rootMinus (t : ℝ) : ℂ := -(27/40:ℂ) * phase t

theorem phase_continuous : Continuous phase := by unfold phase; fun_prop

theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_ne_zero (t : ℝ) : phase t ≠ 0 := by
  exact Complex.exp_ne_zero _

theorem phase_zero : phase 0 = 1 := by simp [phase]
theorem phase_one : phase 1 = -1 := by simp [phase, Complex.exp_pi_mul_I]

theorem phase_mul_star (t : ℝ) : phase t * star (phase t) = 1 := by
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, phase_norm]

theorem sqrtArg_real_lower (t : ℝ) : (11:ℝ)/27 ≤ (sqrtArg t).re := by
  have hn : ‖(star (phase t))^2‖ = 1 := by simp [norm_pow, phase_norm]
  have hr := (abs_le.mp (Complex.abs_re_le_norm ((star (phase t))^2))).1
  rw [hn] at hr
  change -(1:ℝ) ≤ ((starRingEnd ℂ) (phase t)^2).re at hr
  dsimp [sqrtArg]
  norm_num
  linarith

theorem sqrtArg_continuous : Continuous sqrtArg := by
  unfold sqrtArg
  exact continuous_const.add (continuous_const.mul (phase_continuous.star.pow 2))

theorem sqrtArg_sqrt_continuous : Continuous (fun t => Complex.sqrt (sqrtArg t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (Complex.continuousAt_sqrt (Or.inl (by linarith [sqrtArg_real_lower t]))).comp
    sqrtArg_continuous.continuousAt

theorem branch_continuous : Continuous branch := by
  unfold branch
  exact (continuous_const.mul phase_continuous).mul sqrtArg_sqrt_continuous

theorem criticalPlus_continuous : Continuous criticalPlus := by
  unfold criticalPlus
  exact continuous_const.mul (continuous_const.add branch_continuous)

theorem criticalMinus_continuous : Continuous criticalMinus := by
  unfold criticalMinus
  exact continuous_const.mul (continuous_const.sub branch_continuous)

theorem rootPlus_continuous : Continuous rootPlus := by
  unfold rootPlus
  exact continuous_const.mul phase_continuous

theorem rootMinus_continuous : Continuous rootMinus := by
  unfold rootMinus
  exact continuous_const.mul phase_continuous

theorem complex_sqrt_squared (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  exact Complex.cpow_nat_inv_pow z (by decide : (2:ℕ) ≠ 0)

theorem branch_squared (t : ℝ) : branch t ^ 2 = 1 + (27/16:ℂ) * phase t ^ 2 := by
  have hc : ((3 * Real.sqrt 3 / 4 : ℝ) : ℂ)^2 = (27/16:ℂ) := by
    have hr : (3 * Real.sqrt 3 / 4)^2 = (27:ℝ)/16 := by
      calc
        _ = (9/16:ℝ) * (Real.sqrt 3)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num)]; norm_num
    calc
      _ = (((3 * Real.sqrt 3 / 4)^2 : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
      _ = Complex.ofReal ((27:ℝ)/16) := congrArg Complex.ofReal hr
      _ = _ := by norm_num
  have hu := phase_mul_star t
  have hu2 : phase t ^ 2 * star (phase t) ^ 2 = 1 := by
    rw [← mul_pow, hu]
    norm_num
  unfold branch
  rw [mul_pow, mul_pow, complex_sqrt_squared, hc]
  unfold sqrtArg
  linear_combination hu2

theorem branch_ne_zero (t : ℝ) : branch t ≠ 0 := by
  intro h
  have he := branch_squared t
  rw [h, zero_pow (by decide : (2:ℕ) ≠ 0)] at he
  have hmul : (27/16:ℂ) * phase t ^ 2 = -1 := by linear_combination -he
  have hn := congrArg norm hmul
  norm_num [norm_mul, norm_pow, phase_norm] at hn

theorem branch_norm_sq_bound (t : ℝ) : ‖branch t‖^2 ≤ (43:ℝ)/16 := by
  calc
    ‖branch t‖^2 = ‖branch t ^ 2‖ := (norm_pow _ _).symm
    _ = ‖1 + (27/16:ℂ) * phase t ^ 2‖ := by rw [branch_squared]
    _ ≤ ‖(1:ℂ)‖ + ‖(27/16:ℂ) * phase t ^ 2‖ := norm_add_le _ _
    _ = (43:ℝ)/16 := by norm_num [norm_mul, norm_pow, phase_norm]

theorem branch_norm_lt_two (t : ℝ) : ‖branch t‖ < 2 := by
  have h := branch_norm_sq_bound t
  nlinarith [norm_nonneg (branch t)]

theorem rootOne_norm (t : ℝ) : ‖rootOne t‖ = (9:ℝ)/10 := by
  norm_num [rootOne]

theorem rootPlus_norm (t : ℝ) : ‖rootPlus t‖ = (27:ℝ)/40 := by
  norm_num [rootPlus, norm_mul, phase_norm]

theorem rootMinus_norm (t : ℝ) : ‖rootMinus t‖ = (27:ℝ)/40 := by
  norm_num [rootMinus, norm_mul, phase_norm]

theorem criticalPlus_norm_lt (t : ℝ) : ‖criticalPlus t‖ < (9:ℝ)/10 := by
  have he : ‖criticalPlus t‖ = (3:ℝ)/10 * ‖1 + branch t‖ := by
    norm_num [criticalPlus, norm_mul]
  have h := norm_add_le (1:ℂ) (branch t)
  norm_num at h
  rw [he]
  linarith [branch_norm_lt_two t]

theorem criticalMinus_norm_lt (t : ℝ) : ‖criticalMinus t‖ < (9:ℝ)/10 := by
  have he : ‖criticalMinus t‖ = (3:ℝ)/10 * ‖1 - branch t‖ := by
    norm_num [criticalMinus, norm_mul]
  have h := norm_sub_le (1:ℂ) (branch t)
  norm_num at h
  rw [he]
  linarith [branch_norm_lt_two t]

theorem critical_branches_ne (t : ℝ) : criticalPlus t ≠ criticalMinus t := by
  intro h
  have he : branch t = 0 := by
    unfold criticalPlus criticalMinus at h
    linear_combination (5/3:ℂ)*h
  exact branch_ne_zero t he

theorem branch_zero_real :
    branch 0 = ((3 * Real.sqrt 3 / 4 * Real.sqrt ((43:ℝ)/27) : ℝ) : ℂ) := by
  have hh : sqrtArg 0 = (43/27:ℂ) := by norm_num [sqrtArg, phase_zero]
  have hs : Complex.sqrt (sqrtArg 0) = ((Real.sqrt ((43:ℝ)/27) : ℝ) : ℂ) := by
    rw [hh, Complex.sqrt_of_nonneg (by norm_num [Complex.nonneg_iff] : (0:ℂ) ≤ 43/27)]
    norm_num
  unfold branch
  rw [phase_zero, hs, mul_one]
  push_cast
  ring

theorem branch_one_flip : branch 1 = - branch 0 := by
  simp [branch, sqrtArg, phase_one, phase_zero]

theorem branch_zero_re_gt : (3:ℝ)/2 < (branch 0).re := by
  have hp : 0 < (branch 0).re := by
    rw [branch_zero_real]
    simp only [Complex.ofReal_re]
    positivity
  have hi : (branch 0).im = 0 := by rw [branch_zero_real]; rfl
  have he := congrArg Complex.re (branch_squared 0)
  norm_num [pow_two, Complex.mul_re, phase_zero, hi] at he
  nlinarith

theorem bad_minus_endpoint : (21:ℝ)/20 < ‖rootOne 0 - criticalMinus 0‖ := by
  unfold rootOne criticalMinus
  have hr := Complex.re_le_norm (rootOne 0 - criticalMinus 0)
  have hq := branch_zero_re_gt
  norm_num [rootOne, criticalMinus] at hr
  linarith

theorem plus_one_eq_minus_zero : criticalPlus 1 = criticalMinus 0 := by
  simp [criticalPlus, criticalMinus, branch_one_flip, sub_eq_add_neg]

theorem bad_plus_endpoint : (21:ℝ)/20 < ‖rootOne 1 - criticalPlus 1‖ := by
  rw [plus_one_eq_minus_zero]
  exact bad_minus_endpoint

end CStarSendov
