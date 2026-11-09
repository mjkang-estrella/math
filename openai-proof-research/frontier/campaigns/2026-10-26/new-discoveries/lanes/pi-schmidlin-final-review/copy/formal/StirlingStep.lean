import PolynomialBound

namespace Schmidlin

noncomputable def step (z : ℝ) : ℝ :=
  (z+1/2)*Real.log (1+1/z)-1

noncomputable def stepUpper (z : ℝ) : ℝ :=
  (2*z+1)*(1/(2*z+1)+(1/(2*z+1))^3/3+(1/(2*z+1))^5/5+
    (1/(2*z+1))^7/7+(1/(2*z+1))^9/(1-(1/(2*z+1))^2))-1

theorem step_le_stepUpper {z : ℝ} (hz : 0 < z) : step z ≤ stepUpper z := by
  have hd : 0 < 2*z+1 := by linarith
  have hv0 : 0 ≤ 1/(2*z+1) := by positivity
  have hv1 : 1/(2*z+1) < 1 := by apply (div_lt_one hd).2; linarith
  have h := Real.log_div_le_sum_range_add hv0 hv1 4
  norm_num [Finset.sum_range_succ] at h
  have he : (1+1/(2*z+1))/(1-1/(2*z+1)) = 1+1/z := by
    have hi : 1-1/(2*z+1) ≠ 0 := by linarith
    field_simp
    ring
  simp only [one_div] at he
  rw [he] at h
  have hm := mul_le_mul_of_nonneg_left h hd.le
  unfold step stepUpper
  simp only [one_div, inv_pow]
  linarith

noncomputable def stepNumerator (z : ℝ) : ℝ :=
  112*z^8+448*z^7+1295*z^6+2317*z^5+2200*z^4+1061*z^3+253*z^2+34*z+2

theorem stepNumerator_pos {z : ℝ} (hz : 0 < z) : 0 < stepNumerator z := by
  unfold stepNumerator
  positivity

theorem upper_step_identity {z : ℝ} (hz : 0 < z) :
    stirlingUpper z - stirlingUpper (z+1) - stepUpper z =
    stepNumerator z / (2520*z^5*(z+1)^5*(2*z+1)^6) := by
  have h1 : 0 < z+1 := by linarith
  have h2 : 0 < 2*z+1 := by linarith
  have h3 : 1-1/(2*z+1)^2 ≠ 0 := by
    have : 1/(2*z+1) < 1 := by apply (div_lt_one h2).2; linarith
    have : (1/(2*z+1))^2 < 1 := by nlinarith [show 0 < 1/(2*z+1) by positivity]
    simpa only [div_pow, one_pow] using ne_of_gt (sub_pos.mpr this)
  have hd : 2520*z^5*(z+1)^5*(2*z+1)^6 ≠ 0 := by positivity
  apply (eq_div_iff hd).2
  unfold stirlingUpper stepUpper stepNumerator
  field_simp [ne_of_gt hz, ne_of_gt h1, ne_of_gt h2, h3]
  ring_nf
  field_simp [show z*4+z^2*4 ≠ 0 by positivity]
  ring

theorem stirlingUpper_step {z : ℝ} (hz : 0 < z) :
    step z < stirlingUpper z - stirlingUpper (z+1) := by
  have hs := step_le_stepUpper hz
  have h1 : 0 < z+1 := by linarith
  have h2 : 0 < 2*z+1 := by linarith
  have hd : 0 < 2520*z^5*(z+1)^5*(2*z+1)^6 := by positivity
  have hp := div_pos (stepNumerator_pos hz) hd
  rw [← upper_step_identity hz] at hp
  linarith

end Schmidlin
