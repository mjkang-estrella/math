import GapAnalytic
set_option autoImplicit false
set_option warningAsError true
namespace LogArctangentSource

theorem centered_ne {t : ℝ} (ht : 0 < t) : Real.exp (-t) ≠ Real.exp t :=
  (Real.exp_lt_exp.mpr (by linarith)).ne

theorem centered_mean {t : ℝ} (ht : 0 < t) :
    mean (Real.exp (-t)) (Real.exp t) =
      Real.sqrt 2 * Real.sinh t / Real.arctan (Real.sqrt 2*t) := by
  rw [mean, ite_eq_right (centered_ne ht), Real.log_exp, Real.log_exp]
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have harg : (t - -t)/Real.sqrt 2 = Real.sqrt 2*t := by
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [harg, Real.sinh_eq]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem centered_fixedS {t : ℝ} (ht : 0 < t) :
    fixedS (Real.exp (-t)) (Real.exp t) =
      (beta * Real.sinh (alpha*t)/(alpha * Real.sinh (beta*t))) ^ (1/d) := by
  rw [fixedS_formula (centered_ne ht)]
  congr 1
  simp only [← Real.exp_mul, neg_mul]
  rw [show t*alpha = alpha*t by ring, show t*beta = beta*t by ring]
  rw [Real.sinh_eq, Real.sinh_eq]
  field_simp

theorem centered_log_fixedS {t : ℝ} (ht : 0 < t) :
    Real.log (fixedS (Real.exp (-t)) (Real.exp t)) =
      (1/d) * Real.log (beta * Real.sinh (alpha*t)/(alpha * Real.sinh (beta*t))) := by
  rw [centered_fixedS ht, Real.log_rpow]
  exact div_pos (mul_pos parameters.1 (Real.sinh_pos_iff.mpr
    (mul_pos (parameters.1.trans parameters.2.1) ht)))
    (mul_pos (parameters.1.trans parameters.2.1)
      (Real.sinh_pos_iff.mpr (mul_pos parameters.1 ht)))

end LogArctangentSource
namespace LogArctangentMean
open LogArctangentSource (alpha beta)
theorem A_over_B {t : ℝ} (ht : 0 < t) :
    A t / B t = Real.cosh t / Real.sinh t -
      (alpha * (Real.cosh (alpha*t)/Real.sinh (alpha*t)) -
        beta * (Real.cosh (beta*t)/Real.sinh (beta*t)))/d := by
  have hst := (Real.sinh_pos_iff.mpr ht).ne'
  have hsa := (Real.sinh_pos_iff.mpr (mul_pos
    (LogArctangentSource.parameters.1.trans LogArctangentSource.parameters.2.1) ht)).ne'
  have hsb := (Real.sinh_pos_iff.mpr (mul_pos LogArctangentSource.parameters.1 ht)).ne'
  have hp : Real.sinh (alpha*t)*Real.sinh (beta*t) =
      (Real.cosh (5*t)-Real.cosh (d*t))/2 := by
    have h := B_factor t
    unfold B at h
    exact (mul_left_cancel₀ hst (by nlinarith [h]))
  have hm : alpha*Real.cosh (alpha*t)*Real.sinh (beta*t) -
      beta*Real.sinh (alpha*t)*Real.cosh (beta*t) =
      (d*Real.sinh (5*t)-5*Real.sinh (d*t))/2 := by
    have hs : alpha*t+beta*t=5*t := by dsimp [alpha,beta]; ring
    have hd : alpha*t-beta*t=d*t := by dsimp [alpha,beta]; rw [d_source]; ring
    rw [← hs, ← hd, Real.sinh_add, Real.sinh_sub]
    dsimp [alpha,beta]; rw [← d_source]; ring
  have hc := Real.cosh_sub (5*t) t
  rw [show 5*t-t=4*t by ring] at hc
  rw [B_factor]
  unfold A
  have hsa' : Real.sinh (t*alpha) ≠ 0 := by simpa [mul_comm] using hsa
  have hsb' : Real.sinh (t*beta) ≠ 0 := by simpa [mul_comm] using hsb
  field_simp [d_ne, hsa, hsb, hsa', hsb']
  simp only [mul_comm alpha t, mul_comm beta t, mul_comm d t] at hp hm hc
  linear_combination -d * Real.cosh t * (2 * hp) +
    2 * Real.sinh t * hm + d * hc
end LogArctangentMean
