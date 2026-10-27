import Entropy

namespace Schmidlin

noncomputable def sourceK : ℝ := 12*(Real.exp (1/48)-1)

theorem sourceK_lower : (1:ℝ)/4 ≤ sourceK := by
  have h := Real.add_one_le_exp (1/48 : ℝ)
  unfold sourceK
  linarith

theorem sourceK_upper : sourceK < 1/2 := by
  have h := Real.exp_bound_div_one_sub_of_interval
    (x := (1:ℝ)/48) (by norm_num) (by norm_num)
  norm_num at h
  unfold sourceK
  linarith

theorem stirlingUpper_le {z : ℝ} (hz : 1 ≤ z) :
    stirlingUpper z ≤ 1/(12*z) := by
  have hz0 : 0 < z := by linarith
  have h1 : (0:ℝ) < 360*z^3 := by positivity
  have h2 : (0:ℝ) < 1260*z^5 := by positivity
  have hden : 360*z^3 ≤ 1260*z^5 := by
    have hp : z^2 ≥ 1 := by nlinarith
    nlinarith only [mul_nonneg (show 0 ≤ z^3 by positivity) (show 0 ≤ 1260*z^2-360 by linarith)]
  have h := (one_div_le_one_div_of_le h1 hden)
  unfold stirlingUpper
  linarith

theorem scalar_bound {z a r : ℝ} (hz : 1 ≤ z) (ha : -(1:ℝ)/2 ≤ a)
    (hr : r ≤ stirlingUpper z) :
    r-entropy z a < 1/(12*(z+a)-sourceK) := by
  have hz0 : 0 < z := by linarith
  have hza : 0 < z+a := by linarith
  have hd : 0 < 12*(z+a)-sourceK := by have := sourceK_upper; linarith
  have hd' : 0 < 12*(z+a)-(1:ℝ)/4 := by linarith
  have hcomp : 1/(12*(z+a)-(1:ℝ)/4) ≤ 1/(12*(z+a)-sourceK) := by
    apply one_div_le_one_div_of_le hd
    have := sourceK_lower
    linarith
  by_cases hsign : 0 ≤ a
  · have h := rational_gap_pos hz hsign
    have he := entropy_lower hz0 hsign
    linarith
  · have han : a < 0 := lt_of_not_ge hsign
    have he := entropy_nonneg hz0 hza
    have hu := stirlingUpper_le hz
    have hp : 1/(12*z) < 1/(12*(z+a)-sourceK) := by
      apply one_div_lt_one_div_of_lt hd
      have := sourceK_lower
      linarith
    linarith

end Schmidlin
