import PolynomialBound

namespace Schmidlin

noncomputable def entropy (z a : ℝ) : ℝ :=
  (z+a)*Real.log (1+a/z)-a

theorem entropy_nonneg {z a : ℝ} (hz : 0 < z) (ha : 0 < z+a) :
    0 ≤ entropy z a := by
  have ht : 0 < 1+a/z := by apply (div_pos ha hz).trans_eq; field_simp
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ht) ha.le
  have hi : (z+a)*(1-(1+a/z)⁻¹) = a := by field_simp; ring
  rw [hi] at h
  unfold entropy
  linarith

theorem entropy_lower {z a : ℝ} (hz : 0 < z) (ha : 0 ≤ a) :
    a^2/(2*z+a) ≤ entropy z a := by
  have ht : 0 ≤ a/z := div_nonneg ha hz.le
  have h := mul_le_mul_of_nonneg_left (Real.le_log_one_add_of_nonneg ht)
    (show 0 ≤ z+a by linarith)
  have hi : (z+a)*(2*(a/z)/(a/z+2)) - a = a^2/(2*z+a) := by
    have h1 : a/z+2 ≠ 0 := by positivity
    have h2 : 2*z+a ≠ 0 := by linarith
    field_simp
    ring
  unfold entropy
  linarith

end Schmidlin
