import SourceBridge
import GammaUpper

namespace Schmidlin

theorem source_strict_bound {x alpha : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ alpha) :
    sourceError x alpha < 1/(12*(x+alpha)+18-12*Real.exp (1/48)) := by
  rw [sourceError_expanded hx ha, expandedError_identity hx ha]
  have hz : 1 ≤ x+1 := by linarith
  have ha' : -(1:ℝ)/2 ≤ alpha-1/2 := by linarith
  have hr := gammaError_le_stirlingUpper (show 0 < x+1 by linarith)
  have h := scalar_bound hz ha' hr
  convert h using 1
  unfold sourceK
  congr 1
  ring

theorem source_conjecture_372858 : SourceConjecture372858 := by
  intro x alpha hx ha _
  exact (source_strict_bound hx ha).le

end Schmidlin
