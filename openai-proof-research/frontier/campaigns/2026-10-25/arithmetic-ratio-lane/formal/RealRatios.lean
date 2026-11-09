import Mathlib

namespace RealRatios

noncomputable def simple (r t : ℝ) : ℝ :=
  r / (1 + t) + 1 / (r + t) + t / (r + 1)

theorem simple_vertical_identity {r t : ℝ} (hr : 0 < r) (ht : 1 ≤ t) :
    simple r t - simple r 1 =
      (t - 1) * (2 * (t - 1)^2 + (4 + r - r^2) * (t - 1) +
        r * (1-r) * (r+3)) / (2 * (t+1) * (r+t) * (r+1)) := by
  unfold simple
  field_simp
  nlinarith [sq_nonneg r, sq_nonneg t]

theorem simple_vertical {r t : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ht : 1 ≤ t) :
    simple r 1 ≤ simple r t := by
  apply sub_nonneg.mp
  rw [simple_vertical_identity hr ht]
  have h1 : 0 ≤ 1-r := by linarith
  have h2 : 0 ≤ t-1 := by linarith
  have hc : 0 ≤ 4+r-r^2 := by nlinarith [mul_nonneg hr.le h1]
  apply div_nonneg
  · positivity
  · positivity

theorem simple_horizontal_identity {r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    simple r 1 - simple q 1 =
      (q-r) * (4-(1+r)*(1+q)) / (2*(1+r)*(1+q)) := by
  unfold simple
  field_simp
  ring

theorem simple_horizontal {r q : ℝ} (hr : 0 < r) (hrq : r ≤ q) (hq1 : q ≤ 1) :
    simple q 1 ≤ simple r 1 := by
  have hq : 0 < q := lt_of_lt_of_le hr hrq
  apply sub_nonneg.mp
  rw [simple_horizontal_identity hr hq]
  have hdiff : 0 ≤ q-r := sub_nonneg.mpr hrq
  have hprod : (1+r)*(1+q) ≤ (2:ℝ)*2 :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have hcoef : 0 ≤ 4-(1+r)*(1+q) := by linarith
  exact div_nonneg (mul_nonneg hdiff hcoef) (by positivity)

theorem simple_normalized_bound {r q t : ℝ}
    (hr : 0 < r) (hrq : r ≤ q) (hq1 : q ≤ 1) (ht : 1 ≤ t) :
    simple q 1 ≤ simple r t :=
  le_trans (simple_horizontal hr hrq hq1) (simple_vertical hr (hrq.trans hq1) ht)

noncomputable def mixed (r t : ℝ) : ℝ :=
  r*(1+t)/(r*t+r+2*t) + (r+t)/(2*r*t+r+t) + t*(r+1)/(r*t+2*r+t)

noncomputable def certificate (r v : ℝ) : ℝ :=
  (2*r^4+4*r^3+7*r^2+8*r+3)*v^2 +
  (4*r^4-5*r^3+8*r^2+19*r+6)*v + (1-r)*(3*r+1)*(5*r+3)

theorem mixed_vertical_identity {r t : ℝ} (hr : 0 < r) (ht : 1 ≤ t) :
    mixed r t - mixed r 1 =
      r*(t-1)*certificate r (t-1) /
      ((r+1)*(3*r+1)*(r*t+r+2*t)*(r*t+2*r+t)*(2*r*t+r+t)) := by
  have ht0 : 0 < t := by linarith
  unfold mixed certificate
  field_simp
  ring

theorem certificate_nonneg {r v : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hv : 0 ≤ v) :
    0 ≤ certificate r v := by
  have hdiff : 0 ≤ 1-r := by linarith
  have hb : 4*r^4-5*r^3+8*r^2+19*r+6 =
      4*r^4 + 5*r^2*(1-r) + 3*r^2 + 19*r+6 := by ring
  unfold certificate
  rw [hb]
  positivity

theorem mixed_vertical {r t : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ht : 1 ≤ t) :
    mixed r 1 ≤ mixed r t := by
  apply sub_nonneg.mp
  rw [mixed_vertical_identity hr ht]
  have ht0 : 0 < t := by linarith
  have hv : 0 ≤ t-1 := by linarith
  have hp := certificate_nonneg hr hr1 hv
  positivity

theorem mixed_horizontal_identity {r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    mixed r 1 - mixed q 1 =
      (q-r)*(3+r+q-5*r*q)/((r+1)*(q+1)*(3*r+1)*(3*q+1)) := by
  unfold mixed
  field_simp
  ring

theorem mixed_horizontal {r q : ℝ} (hr : 0 < r) (hrq : r ≤ q) (hq1 : q ≤ 1) :
    mixed q 1 ≤ mixed r 1 := by
  have hq : 0 < q := lt_of_lt_of_le hr hrq
  apply sub_nonneg.mp
  rw [mixed_horizontal_identity hr hq]
  have hdiff : 0 ≤ q-r := sub_nonneg.mpr hrq
  have hmul : r*q ≤ r := by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hq1)]
  have hc : 0 ≤ 3+r+q-5*r*q := by nlinarith
  positivity

theorem mixed_normalized_bound {r q t : ℝ}
    (hr : 0 < r) (hrq : r ≤ q) (hq1 : q ≤ 1) (ht : 1 ≤ t) :
    mixed q 1 ≤ mixed r t :=
  le_trans (mixed_horizontal hr hrq hq1) (mixed_vertical hr (hrq.trans hq1) ht)

end RealRatios
