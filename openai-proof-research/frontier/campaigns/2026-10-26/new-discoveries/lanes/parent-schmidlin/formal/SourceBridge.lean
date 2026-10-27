import SourceDefs
import ScalarBound

namespace Schmidlin

theorem sourceError_expanded {x alpha : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ alpha) :
    sourceError x alpha = expandedError x alpha := by
  have hx1 : 0 < x+1 := by linarith
  have hy : 0 < x+alpha+1/2 := by linarith
  have hg := Real.Gamma_pos_of_pos hx1
  unfold sourceError interpolatedPi burnsideStirling expandedError
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (ne_of_gt hg) (by positivity), Real.log_rpow hx1,
    Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hy,
    Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_sqrt]
  · ring
  · positivity

theorem expandedError_identity {x alpha : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ alpha) :
    expandedError x alpha = gammaError (x+1)-entropy (x+1) (alpha-1/2) := by
  have hx1 : 0 < x+1 := by linarith
  have hy : 0 < x+alpha+1/2 := by linarith
  have hi : 1+(alpha-1/2)/(x+1) = (x+alpha+1/2)/(x+1) := by field_simp; ring
  unfold expandedError gammaError entropy
  rw [hi, Real.log_div (ne_of_gt hy) (ne_of_gt hx1)]
  ring

end Schmidlin
