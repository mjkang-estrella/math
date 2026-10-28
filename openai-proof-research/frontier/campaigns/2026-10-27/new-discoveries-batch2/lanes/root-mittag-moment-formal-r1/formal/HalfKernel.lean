import HalfIntegral

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MittagModulus

noncomputable def halfExpIntegral (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..1, Real.exp (x * u ^ 2)

theorem halfExpIntegral_continuous : Continuous halfExpIntegral := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

theorem mittagReal_half_integral (x : ℝ) :
    mittagReal 1 (3 / 2) (-x) =
      (2 / Real.sqrt Real.pi) * Real.exp (-x) * halfExpIntegral x := by
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have h := integral_halfExp_eq_mittagReal x
  have he : (fun u : ℝ => Real.exp (-x * (1 - u ^ 2))) =
      (fun u : ℝ => Real.exp (-x) * Real.exp (x * u ^ 2)) := by
    funext u
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, intervalIntegral.integral_const_mul] at h
  change Real.exp (-x) * halfExpIntegral x = _ at h
  field_simp
  nlinarith

theorem mittag_half_imaginary (r : ℝ) :
    mittagLeffler (1 / 2) 1 ((r : ℂ) * Complex.I) =
      (Real.exp (-(r ^ 2)) : ℂ) +
        (((2 * r / Real.sqrt Real.pi) * Real.exp (-(r ^ 2)) *
          halfExpIntegral (r ^ 2) : ℝ) : ℂ) * Complex.I := by
  rw [mittagLeffler_even_odd (by norm_num : (0 : ℝ) < 1 / 2) zero_lt_one]
  norm_num only at *
  have hz : ((r : ℂ) * Complex.I) ^ 2 = ((-(r ^ 2) : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [hz]
  rw [mittag_one_eq_exp, ← Complex.ofReal_exp, mittagLeffler_ofReal,
    mittagReal_half_integral (r ^ 2)]
  push_cast
  ring

noncomputable def halfProductKernel (v w t : ℝ) : ℝ :=
  Real.exp (-(v + w) * t) *
    (1 + (4 * t * Real.sqrt (v * w) / Real.pi) *
      halfExpIntegral (v * t) * halfExpIntegral (w * t))

theorem halfCross_eq_halfProductKernel {v w t : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w)
    (ht : 0 ≤ t) : halfCross v w t = halfProductKernel v w t := by
  have hr : (Real.sqrt t * Real.sqrt v) ^ 2 = v * t := by
    rw [mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hv]
    ring
  have hs : (Real.sqrt t * Real.sqrt w) ^ 2 = w * t := by
    rw [mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hw]
    ring
  have hzv : (Real.sqrt t : ℂ) * Complex.I * (Real.sqrt v : ℂ) =
      ((Real.sqrt t * Real.sqrt v : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hzw : (Real.sqrt t : ℂ) * Complex.I * (Real.sqrt w : ℂ) =
      ((Real.sqrt t * Real.sqrt w : ℝ) : ℂ) * Complex.I := by push_cast; ring
  unfold halfCross
  rw [hzv, hzw, mittag_half_imaginary, mittag_half_imaginary, hr, hs]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.neg_re, Complex.neg_im]
  unfold halfProductKernel
  have he : Real.exp (-(v + w) * t) = Real.exp (-(v * t)) * Real.exp (-(w * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, Real.sqrt_mul hv w]
  have hp : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hp0 : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have ht' : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  field_simp
  ring_nf
  rw [hp, ht']
  ring

end MittagModulus
