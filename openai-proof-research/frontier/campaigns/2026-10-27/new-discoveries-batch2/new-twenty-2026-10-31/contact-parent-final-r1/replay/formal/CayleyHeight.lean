import CayleyLocalization
namespace ContactPilot
noncomputable section

/-- Uniform height comparison on a fixed, explicitly bounded chart. -/
theorem beta_height_comparison (y : ℂ) (hi : 0 < y.im) (hy : ‖y‖ < 1/2) :
    y.im/2 ≤ 1-‖beta y‖ ∧ 1-‖beta y‖ ≤ 16*y.im := by
  have hd := beta_denominator_ne y hi.le
  have hb := beta_norm_lt_one y hi
  have hl : 1/2 ≤ ‖1-Complex.I*y‖ := by
    have h := norm_sub_norm_le (1:ℂ) (Complex.I*y)
    simp only [norm_one,norm_mul,Complex.norm_I,one_mul] at h
    linarith
  have hu : ‖1-Complex.I*y‖ ≤ 2 := by
    have h := norm_sub_le (1:ℂ) (Complex.I*y)
    simp only [norm_one,norm_mul,Complex.norm_I,one_mul] at h
    linarith
  have hs : ‖1-Complex.I*y‖^2 - ‖1+Complex.I*y‖^2 = 4*y.im := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  have hn : ‖beta y‖*‖1-Complex.I*y‖ = ‖1+Complex.I*y‖ := by
    change ‖(1+Complex.I*y)/(1-Complex.I*y)‖*_ = _
    rw [norm_div,div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hd)]
  have he : (1-‖beta y‖) * (‖1-Complex.I*y‖^2*(1+‖beta y‖)) = 4*y.im := by
    have hsq := congrArg (fun t : ℝ => t^2) hn
    nlinarith only [hs,hsq]
  have haL : 1/4 ≤ ‖1-Complex.I*y‖^2*(1+‖beta y‖) := by
    have hsL : 1/4 ≤ ‖1-Complex.I*y‖^2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg ‖1-Complex.I*y‖) (norm_nonneg (beta y))]
  have haU : ‖1-Complex.I*y‖^2*(1+‖beta y‖) ≤ 8 := by
    have hsU : ‖1-Complex.I*y‖^2 ≤ 4 := by nlinarith [norm_nonneg (1-Complex.I*y)]
    calc
      _ ≤ ‖1-Complex.I*y‖^2*2 := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ ≤ 8 := by linarith
  constructor
  · nlinarith [mul_nonneg (by linarith : 0 ≤ 1-‖beta y‖)
      (by linarith : 0 ≤ 8-‖1-Complex.I*y‖^2*(1+‖beta y‖))]
  · nlinarith [mul_nonneg (by linarith : 0 ≤ 1-‖beta y‖)
      (by linarith : 0 ≤ ‖1-Complex.I*y‖^2*(1+‖beta y‖)-1/4)]
end
end ContactPilot
