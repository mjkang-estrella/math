import Mathlib

namespace ConnectionGraph

noncomputable def positiveBranch (q : ℝ) : ℝ := (q + Real.sqrt (q ^ 2 + 4)) / 2
noncomputable def branchExcess (q : ℝ) : ℝ := Real.sqrt (q ^ 2 + 4) / 2 - 1

theorem positiveBranch_split (q : ℝ) :
    positiveBranch q = 1 + q / 2 + branchExcess q := by
  unfold positiveBranch branchExcess
  ring

theorem branchExcess_nonneg (q : ℝ) : 0 ≤ branchExcess q := by
  have hs := Real.sq_sqrt (show 0 ≤ q ^ 2 + 4 by positivity)
  have hn := Real.sqrt_nonneg (q ^ 2 + 4)
  unfold branchExcess
  nlinarith [sq_nonneg q]

theorem positiveBranch_pos {q : ℝ} (hq : 0 ≤ q) : 0 < positiveBranch q := by
  rw [positiveBranch_split]
  have := branchExcess_nonneg q
  linarith

theorem branchExcess_mono {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) :
    branchExcess q ≤ branchExcess r := by
  have hs : Real.sqrt (q ^ 2 + 4) ≤ Real.sqrt (r ^ 2 + 4) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  unfold branchExcess
  linarith

theorem positiveBranch_mono {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) :
    positiveBranch q ≤ positiveBranch r := by
  have := branchExcess_mono hq hqr
  rw [positiveBranch_split, positiveBranch_split]
  linarith

theorem positiveBranch_equation (q : ℝ) :
    positiveBranch q ^ 2 - q * positiveBranch q - 1 = 0 := by
  have hs := Real.sq_sqrt (show 0 ≤ q ^ 2 + 4 by positivity)
  unfold positiveBranch
  nlinarith

theorem positiveBranch_eq_add_inv {q : ℝ} (hq : 0 ≤ q) :
    positiveBranch q = q + (positiveBranch q)⁻¹ := by
  have hp := positiveBranch_equation q
  have hn := ne_of_gt (positiveBranch_pos hq)
  apply mul_right_cancel₀ hn
  rw [add_mul, inv_mul_cancel₀ hn]
  nlinarith

theorem branchExcess_two : branchExcess 2 = Real.sqrt 2 - 1 := by
  have h8 := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn8 := Real.sqrt_nonneg (8 : ℝ)
  have hn2 := Real.sqrt_nonneg (2 : ℝ)
  have he : Real.sqrt 8 = 2 * Real.sqrt 2 := by nlinarith
  norm_num [branchExcess]
  linarith

theorem branchExcess_ge_gap {q : ℝ} (hq : 2 ≤ q) :
    Real.sqrt 2 - 1 ≤ branchExcess q := by
  rw [← branchExcess_two]
  exact branchExcess_mono (by norm_num) hq

theorem gap_positive : 0 < Real.sqrt 2 - 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem gap_lt_half : Real.sqrt 2 - 1 < 1 / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem sum_bound_ge_sqrt {k T : ℝ} (hk : 0 ≤ k) (hT : 0 ≤ T) :
    Real.sqrt (2 * k * T) ≤ k + T / 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ 2 * k * T by positivity)
  have hn := Real.sqrt_nonneg (2 * k * T)
  nlinarith [sq_nonneg (k - T / 2)]

theorem sqrt_le_half_add_one {t : ℝ} (ht : 0 ≤ t) : Real.sqrt t ≤ (t + 1) / 2 := by
  have hs := Real.sq_sqrt ht
  have hn := Real.sqrt_nonneg t
  nlinarith [sq_nonneg (Real.sqrt t - 1)]

theorem high_index_gap {v m A B : ℝ} (hv : 1 ≤ v) (hA : v + m ≤ A)
    (hB : B ≤ m + v / 2) : Real.sqrt 2 - 1 ≤ A - B := by
  have := gap_lt_half
  linarith

theorem low_index_gap {k T q A B : ℝ} (hk : 0 ≤ k) (hT : 0 ≤ T) (hq : 2 ≤ q)
    (hA : k + T / 2 + branchExcess q ≤ A) (hB : B ≤ Real.sqrt (2 * k * T)) :
    Real.sqrt 2 - 1 ≤ A - B := by
  have := sum_bound_ge_sqrt hk hT
  have := branchExcess_ge_gap hq
  linarith

end ConnectionGraph
