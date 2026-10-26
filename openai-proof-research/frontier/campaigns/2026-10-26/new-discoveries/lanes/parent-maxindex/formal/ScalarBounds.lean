import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace MaxIndex

/- Scalar ingredients only. These are not the finite-array source theorem. -/

theorem low_maximum_bound (m : ℝ) (hm : 0 ≤ m) :
    (4 * m + 7) / 6 + Real.sqrt (2 * m + 1) < m + 3 := by
  have hs := Real.sq_sqrt (show 0 ≤ 2 * m + 1 by positivity)
  have hn := Real.sqrt_nonneg (2 * m + 1)
  have hg : 0 < (2 * m + 11) / 6 := by positivity
  have hlt : Real.sqrt (2 * m + 1) < (2 * m + 11) / 6 := by
    nlinarith [sq_nonneg (2 * m - 7)]
  linarith

theorem high_maximum_bound (m p : ℝ) (hm : 0 ≤ m)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    1 + (m + 1) * p + Real.sqrt (2 * m) * Real.sqrt (1 - p ^ 2) < m + 3 := by
  have hpp : 0 ≤ 1 - p ^ 2 := by nlinarith
  have ha := Real.sq_sqrt (show 0 ≤ 2 * m by positivity)
  have hb := Real.sq_sqrt hpp
  let a := Real.sqrt (2 * m)
  let b := Real.sqrt (1 - p ^ 2)
  have ha' : a ^ 2 = 2 * m := ha
  have hb' : b ^ 2 = 1 - p ^ 2 := hb
  have hid : (m + 1) ^ 2 + 2 * m - ((m + 1) * p + a * b) ^ 2 =
      ((m + 1) * b - a * p) ^ 2 := by
    nlinarith [sq_nonneg ((m + 1) * b - a * p)]
  have hsq : ((m + 1) * p + a * b) ^ 2 ≤ m ^ 2 + 4 * m + 1 := by
    nlinarith [sq_nonneg ((m + 1) * b - a * p)]
  have hlt : (m + 1) * p + a * b < m + 2 := by
    nlinarith [sq_nonneg ((m + 1) * p + a * b - (m + 2))]
  change 1 + (m + 1) * p + a * b < m + 3
  linarith

theorem sharpness_gap_positive (m : ℝ) (hm : 2 ≤ m) :
    0 < (m - 1) ^ 2 / (4 * m ^ 2 + m) := by
  apply div_pos
  · exact sq_pos_of_pos (by linarith)
  · positivity

theorem sharpness_selected_sum (m : ℝ) (hm : 2 ≤ m) :
    ((m + 3 / 2) * (2 * m) ^ 2 + m) / ((2 * m) ^ 2 + m) +
      ((2 * m) ^ 2 + 2 * m * (2 * m) + 1) / ((2 * m) ^ 2 + m) - (m + 3) =
      (m - 1) ^ 2 / (4 * m ^ 2 + m) := by
  have hd : (2 * m) ^ 2 + m ≠ 0 := by positivity
  have hd' : 4 * m ^ 2 + m ≠ 0 := by positivity
  field_simp
  ring

end MaxIndex
