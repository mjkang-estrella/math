import UnboundedBounds

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CStarSmaleUnbounded

theorem plus_value_gap (epsilon : ℝ) (he : 0 < epsilon) :
    2 < ‖cubicValue (roots epsilon) coordinate - cubicValue (roots epsilon) (branch epsilon)‖ := by
  have hn := (cubicValue (roots epsilon) coordinate -
    cubicValue (roots epsilon) (branch epsilon)).norm_coe_le_norm timeZero
  have hr := Complex.re_le_norm ((cubicValue (roots epsilon) coordinate -
    cubicValue (roots epsilon) (branch epsilon)) timeZero)
  have hg : 2 < ((cubicValue (roots epsilon) coordinate -
      cubicValue (roots epsilon) (branch epsilon)) timeZero).re := by
    rw [value_eq, value_eq]
    change 2 < ((coordinate timeZero) ^ 3 - 3 * (branch epsilon timeZero) ^ 2 * coordinate timeZero -
      ((branch epsilon timeZero) ^ 3 - 3 * (branch epsilon timeZero) ^ 2 * branch epsilon timeZero)).re
    have hc : coordinate timeZero = (-1 : ℂ) := by norm_num [coordinate, timeZero]
    rw [hc]
    have hs := branch_sq epsilon he.le timeZero
    rw [hc] at hs
    have hi : (-1 : ℂ) ^ 3 - 3 * (branch epsilon timeZero) ^ 2 * (-1) -
        ((branch epsilon timeZero) ^ 3 - 3 * (branch epsilon timeZero) ^ 2 * branch epsilon timeZero) =
        2 + 3 * (epsilon : ℂ) + 2 * (branch epsilon timeZero) ^ 3 := by
      linear_combination 3 * hs
    rw [hi]
    norm_num [branch, ← Complex.ofReal_pow, Complex.mul_re, Complex.add_re]
    have hp : 0 ≤ Real.sqrt ((2 * (timeZero : ℝ) - 1) ^ 2 + epsilon) := Real.sqrt_nonneg _
    nlinarith [pow_nonneg hp 3]
  exact hg.trans_le (hr.trans hn)

theorem minus_value_gap (epsilon : ℝ) (he : 0 < epsilon) :
    2 < ‖cubicValue (roots epsilon) coordinate - cubicValue (roots epsilon) (-branch epsilon)‖ := by
  have hn := (cubicValue (roots epsilon) coordinate -
    cubicValue (roots epsilon) (-branch epsilon)).norm_coe_le_norm timeOne
  have hr := (neg_le_abs ((cubicValue (roots epsilon) coordinate -
    cubicValue (roots epsilon) (-branch epsilon)) timeOne).re).trans (Complex.abs_re_le_norm _)
  have hg : 2 < -((cubicValue (roots epsilon) coordinate -
      cubicValue (roots epsilon) (-branch epsilon)) timeOne).re := by
    rw [value_eq, value_eq]
    change 2 < -((coordinate timeOne) ^ 3 - 3 * (branch epsilon timeOne) ^ 2 * coordinate timeOne -
      ((-branch epsilon timeOne) ^ 3 - 3 * (branch epsilon timeOne) ^ 2 * (-branch epsilon timeOne))).re
    have hc : coordinate timeOne = (1 : ℂ) := by norm_num [coordinate, timeOne]
    rw [hc]
    have hs := branch_sq epsilon he.le timeOne
    rw [hc] at hs
    have hi : (1 : ℂ) ^ 3 - 3 * (branch epsilon timeOne) ^ 2 * 1 -
        ((-branch epsilon timeOne) ^ 3 - 3 * (branch epsilon timeOne) ^ 2 * (-branch epsilon timeOne)) =
        -(2 + 3 * (epsilon : ℂ) + 2 * (branch epsilon timeOne) ^ 3) := by
      linear_combination -3 * hs
    rw [hi]
    norm_num [branch, ← Complex.ofReal_pow, Complex.mul_re, Complex.add_re]
    have hp : 0 ≤ Real.sqrt ((2 * (timeOne : ℝ) - 1) ^ 2 + epsilon) := Real.sqrt_nonneg _
    nlinarith [pow_nonneg hp 3]
  exact hg.trans_le (hr.trans hn)

theorem critical_value_gap (epsilon : ℝ) (he : 0 < epsilon)
    (w : FunctionAlgebra) (hw : cubicDeleted (roots epsilon) w = 0) :
    2 < ‖cubicValue (roots epsilon) coordinate - cubicValue (roots epsilon) w‖ := by
  rcases critical_complete epsilon he w hw with rfl | rfl
  · exact plus_value_gap epsilon he
  · exact minus_value_gap epsilon he

end CStarSmaleUnbounded
