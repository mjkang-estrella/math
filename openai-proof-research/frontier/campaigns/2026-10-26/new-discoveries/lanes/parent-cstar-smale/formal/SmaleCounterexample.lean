import SmaleBounds

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CStarSmale

theorem plus_value_gap : 2 < ‖cubicValue roots coordinate - cubicValue roots branch‖ := by
  have hn := (cubicValue roots coordinate - cubicValue roots branch).norm_coe_le_norm timeZero
  have hr := Complex.re_le_norm ((cubicValue roots coordinate - cubicValue roots branch) timeZero)
  have he : 2 < ((cubicValue roots coordinate - cubicValue roots branch) timeZero).re := by
    rw [value_eq, value_eq]
    change 2 < ((coordinate timeZero) ^ 3 - 3 * (branch timeZero) ^ 2 * (coordinate timeZero) -
      ((branch timeZero) ^ 3 - 3 * (branch timeZero) ^ 2 * branch timeZero)).re
    have hc : coordinate timeZero = (-1 : ℂ) := by norm_num [coordinate, timeZero]
    rw [hc]
    have hs := branch_sq timeZero
    change branch timeZero ^ 2 = coordinate timeZero ^ 2 + 1 / 16 at hs
    rw [hc] at hs
    have hid : (-1 : ℂ) ^ 3 - 3 * (branch timeZero) ^ 2 * (-1) -
        ((branch timeZero) ^ 3 - 3 * (branch timeZero) ^ 2 * branch timeZero) =
        35 / 16 + 2 * (branch timeZero) ^ 3 := by
      linear_combination 3 * hs
    rw [hid]
    norm_num [branch, ← Complex.ofReal_pow, Complex.mul_re, Complex.add_re]
    have h : 0 ≤ Real.sqrt ((2 * (timeZero : ℝ) - 1) ^ 2 + 1 / 16) := Real.sqrt_nonneg _
    nlinarith [pow_nonneg h 3]
  exact he.trans_le (hr.trans hn)

theorem minus_value_gap : 2 < ‖cubicValue roots coordinate - cubicValue roots (-branch)‖ := by
  have hn := (cubicValue roots coordinate - cubicValue roots (-branch)).norm_coe_le_norm timeOne
  have hr := (neg_le_abs ((cubicValue roots coordinate - cubicValue roots (-branch)) timeOne).re).trans
    (Complex.abs_re_le_norm _)
  have he : 2 < -((cubicValue roots coordinate - cubicValue roots (-branch)) timeOne).re := by
    rw [value_eq, value_eq]
    change 2 < -((coordinate timeOne) ^ 3 - 3 * (branch timeOne) ^ 2 * (coordinate timeOne) -
      ((-branch timeOne) ^ 3 - 3 * (branch timeOne) ^ 2 * (-branch timeOne))).re
    have hc : coordinate timeOne = (1 : ℂ) := by norm_num [coordinate, timeOne]
    rw [hc]
    have hs := branch_sq timeOne
    change branch timeOne ^ 2 = coordinate timeOne ^ 2 + 1 / 16 at hs
    rw [hc] at hs
    have hid : (1 : ℂ) ^ 3 - 3 * (branch timeOne) ^ 2 * 1 -
        ((-branch timeOne) ^ 3 - 3 * (branch timeOne) ^ 2 * (-branch timeOne)) =
        -(35 / 16 + 2 * (branch timeOne) ^ 3) := by
      linear_combination -3 * hs
    rw [hid]
    norm_num [branch, ← Complex.ofReal_pow, Complex.mul_re, Complex.add_re]
    have h : 0 ≤ Real.sqrt ((2 * (timeOne : ℝ) - 1) ^ 2 + 1 / 16) := Real.sqrt_nonneg _
    nlinarith [pow_nonneg h 3]
  exact he.trans_le (hr.trans hn)

theorem critical_value_gap (w : FunctionAlgebra) (hw : cubicDeleted roots w = 0) :
    2 < ‖cubicValue roots coordinate - cubicValue roots w‖ := by
  rcases critical_complete w hw with rfl | rfl
  · exact plus_value_gap
  · exact minus_value_gap

theorem critical_distance_le (w : FunctionAlgebra) (hw : cubicDeleted roots w = 0) :
    ‖coordinate - w‖ ≤ 9 / 4 := by
  rcases critical_complete w hw with rfl | rfl
  · exact distance_plus_le
  · exact distance_minus_le

theorem critical_distance_pos (w : FunctionAlgebra) (hw : cubicDeleted roots w = 0) :
    0 < ‖coordinate - w‖ := by
  apply norm_pos_iff.mpr
  intro he
  have hc : coordinate = w := sub_eq_zero.mp he
  exact deleted_coordinate_ne (hc.symm ▸ hw)

theorem source_counterexample_cubic : ¬SourceCubicClaim FunctionAlgebra := by
  intro h
  obtain ⟨w, hw, hbound⟩ := h roots coordinate deleted_coordinate_ne
  have hpos := critical_distance_pos w hw
  have hgap := critical_value_gap w hw
  have hdist := critical_distance_le w hw
  rw [deleted_coordinate_norm] at hbound
  have hh := (div_le_iff₀ hpos).mp hbound
  nlinarith

end CStarSmale
