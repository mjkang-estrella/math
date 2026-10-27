import Mathlib

set_option warningAsError true

namespace SquaredPolya

noncomputable def scalarDefect : ℝ :=
  (1025 / 64 : ℝ)^2 *
      ((2048 / 1054721 : ℝ) * (1058845 / 8) +
        Real.sqrt (2048 / 1054721) * (17463 / 2) + 257) -
    ((1050641 / 4 : ℝ) + Real.sqrt (4100 / 1054721) * (1056799 / 4) +
        (4100 / 1054721) * (1058845 / 8)) /
      ((1058821 / 1054721 : ℝ) + 2 * Real.sqrt (4100 / 1054721))

theorem scalarDefect_lt : scalarDefect < -17000 := by
  let a : ℝ := Real.sqrt (2048 / 1054721)
  let b : ℝ := Real.sqrt (4100 / 1054721)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = (2048 / 1054721 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hb2 : b ^ 2 = (4100 / 1054721 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have haU : a ≤ (441 / 10000 : ℝ) := by nlinarith
  have hbL : (623 / 10000 : ℝ) ≤ b := by nlinarith
  have hbU : b ≤ (624 / 10000 : ℝ) := by nlinarith
  let L : ℝ := (1050641 / 4 : ℝ) + (623 / 10000) * (1056799 / 4) +
    (4100 / 1054721) * (1058845 / 8)
  let U : ℝ := (1058821 / 1054721 : ℝ) + 2 * (624 / 10000)
  let C : ℝ := (2048 / 1054721 : ℝ) * (1058845 / 8) +
    (441 / 10000) * (17463 / 2) + 257
  have hR : 0 < (1058821 / 1054721 : ℝ) + 2 * b := by positivity
  have hRU : (1058821 / 1054721 : ℝ) + 2 * b ≤ U := by dsimp [U]; linarith
  have hLU : 0 ≤ L / U := by dsimp [L, U]; positivity
  have hMul : L / U * U = L := by dsimp [U]; field_simp
  have hN : L ≤ (1050641 / 4 : ℝ) + b * (1056799 / 4) +
      (4100 / 1054721) * (1058845 / 8) := by dsimp [L]; nlinarith
  have hD : L / U ≤
      ((1050641 / 4 : ℝ) + b * (1056799 / 4) +
        (4100 / 1054721) * (1058845 / 8)) /
        ((1058821 / 1054721 : ℝ) + 2 * b) := by
    apply (le_div_iff₀ hR).2
    nlinarith
  have hC : (2048 / 1054721 : ℝ) * (1058845 / 8) +
      a * (17463 / 2) + 257 ≤ C := by dsimp [C]; nlinarith
  have hGap : (1025 / 64 : ℝ)^2 * C - L / U < -17000 := by
    norm_num [C, L, U]
  change (1025 / 64 : ℝ)^2 *
      ((2048 / 1054721 : ℝ) * (1058845 / 8) + a * (17463 / 2) + 257) -
    ((1050641 / 4 : ℝ) + b * (1056799 / 4) +
      (4100 / 1054721) * (1058845 / 8)) /
      ((1058821 / 1054721 : ℝ) + 2 * b) < -17000
  nlinarith


end SquaredPolya
