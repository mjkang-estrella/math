/- Independent controls; Myeongjin Kang. MIT. -/
import Mathlib.Tactic
open scoped ComplexConjugate
namespace ReviewAlgebra
-- Failure weight<=1 and nonnegative acceptance are both semantically needed.
theorem failure_weight_above_one_counterexample :
    ¬ ((2 : ℝ) * (1 / 2) ≤ 1 / 2) := by norm_num

theorem negative_probability_counterexample :
    ¬ ((0 : ℝ) * (-1) ≤ -1) := by norm_num

-- Algebraic averaging can be idempotent without being orthogonal.
def oblique (v : ℂ × ℂ) : ℂ × ℂ := (v.1 + v.2, 0)
def involution (v : ℂ × ℂ) : ℂ × ℂ := (v.1 + 2 * v.2, -v.2)
def euclideanPair (v w : ℂ × ℂ) : ℂ := star v.1 * w.1 + star v.2 * w.2

theorem involution_square (v : ℂ × ℂ) : involution (involution v) = v := by
  apply Prod.ext
  · change v.1 + 2 * v.2 + 2 * (-v.2) = v.1
    ring
  · change -(-v.2) = v.2
    simp

theorem oblique_is_average (v : ℂ × ℂ) :
    oblique v = ((v.1 + (involution v).1) / 2, (v.2 + (involution v).2) / 2) := by
  apply Prod.ext
  · change v.1 + v.2 = (v.1 + (v.1 + 2 * v.2)) / 2
    ring
  · change (0 : ℂ) = (v.2 + -v.2) / 2
    simp

theorem oblique_idempotent (v : ℂ × ℂ) : oblique (oblique v) = oblique v := by
  simp [oblique]

theorem oblique_not_selfadjoint :
    euclideanPair (oblique (0, 1)) (1, 0) ≠
      euclideanPair (0, 1) (oblique (1, 0)) := by
  norm_num [euclideanPair, oblique]

end ReviewAlgebra
