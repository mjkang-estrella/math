import T298P
namespace T298PControls
-- Nonzero coefficients: k=2, epsilon=1, Phi=1 gives 1/16, not 1/4.
theorem wrong_normalization : (1 / (1 * (2:ℝ)^2))^2 ≠ 1 / (1^2 * (2:ℝ)^2) := by norm_num
-- All increment bounds hold, but without micro1 <= star1 the conclusion fails.
theorem missing_comparison :
    (1:ℝ) * (1-0) ≤ 1-0 ∧ 0-0 ≤ 1*(1-1) ∧ ¬ (1*((1-0)-(1-1)) ≤ 0-0) := by norm_num
-- The transferred lower bound is g0-g1, not g1-g0.
theorem wrong_gap_sign :
    (0:ℝ) ≤ 0 ∧ (0-1:ℝ) ≤ 0-1 ∧ (0-0:ℝ) ≤ 1-1 ∧
    ¬ ((1:ℝ) * ((1-0)-(1-1)) ≤ 0-1) := by norm_num
-- All bounds hold at an error equal to half the positive source gap.
theorem equality_errors_not_strict :
    (0:ℝ) ≤ 0 ∧ (1-0:ℝ)-1 ≤ 0-0 ∧ (0-0:ℝ) ≤ 2-2 ∧
    (0:ℝ) < 2-0 ∧ (2-1:ℝ) ≤ (2-0)/2 ∧
    (1:ℝ) = (2-0)/2 ∧ ¬ ((0:ℝ)<0) := by norm_num
end T298PControls
