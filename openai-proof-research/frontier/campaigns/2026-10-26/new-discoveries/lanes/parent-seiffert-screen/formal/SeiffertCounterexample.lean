import Mathlib

namespace SeiffertQuestion

noncomputable def harmonic (x y : ℝ) : ℝ := 2 * x * y / (x + y)
noncomputable def quadratic (x y : ℝ) : ℝ := Real.sqrt ((x ^ 2 + y ^ 2) / 2)
noncomputable def seiffert (x y : ℝ) : ℝ :=
  if x = y then x else (x - y) / (2 * Real.arcsin ((x - y) / (x + y)))

theorem cos_twentieth_upper : Real.cos (1 / 20 : ℝ) < 9999 / 10000 := by
  have hb := le_of_abs_le (Real.cos_bound (x := (1 / 20 : ℝ)) (by norm_num))
  norm_num at hb ⊢
  linarith

theorem arcsin_cos_twentieth :
    Real.arcsin (Real.cos (1 / 20 : ℝ)) = Real.pi / 2 - 1 / 20 := by
  rw [← Real.sin_pi_div_two_sub]
  apply Real.arcsin_sin
  · linarith [Real.pi_gt_three]
  · linarith

theorem arcsin_witness_lower : (29 / 20 : ℝ) < Real.arcsin (9999 / 10000) := by
  have hm := Real.arcsin_lt_arcsin (Real.neg_one_le_cos (1 / 20 : ℝ))
    cos_twentieth_upper (show (9999 / 10000 : ℝ) ≤ 1 by norm_num)
  rw [arcsin_cos_twentieth] at hm
  linarith [Real.pi_gt_three]

theorem quadratic_witness_lower : (14000 : ℝ) ≤ quadratic 19999 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ ((19999 : ℝ) ^ 2 + 1 ^ 2) / 2 by norm_num)
  have hn := Real.sqrt_nonneg (((19999 : ℝ) ^ 2 + 1 ^ 2) / 2)
  unfold quadratic
  nlinarith

theorem seiffert_witness_upper : 2 * seiffert 19999 1 < (400000 / 29 : ℝ) := by
  have ha := arcsin_witness_lower
  have hap : 0 < Real.arcsin (9999 / 10000 : ℝ) := by linarith
  norm_num [seiffert]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hap)).mpr
  nlinarith

theorem source_counterexample_338822 :
    (0 : ℝ) < 19999 ∧ (0 : ℝ) < 1 ∧
      2 * seiffert 19999 1 < quadratic 19999 1 + harmonic 19999 1 := by
  have hq := quadratic_witness_lower
  have hp := seiffert_witness_upper
  have hh : 0 ≤ harmonic 19999 1 := by norm_num [harmonic]
  constructor
  · norm_num
  constructor
  · norm_num
  · linarith

end SeiffertQuestion
