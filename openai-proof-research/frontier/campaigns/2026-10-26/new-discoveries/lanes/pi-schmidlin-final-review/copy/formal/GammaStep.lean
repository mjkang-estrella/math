import SourceDefs
import StirlingStep

namespace Schmidlin

theorem gammaError_step {z : ℝ} (hz : 0 < z) :
    gammaError z-gammaError (z+1) = step z := by
  have hg := Real.Gamma_pos_of_pos hz
  have hr := Real.Gamma_add_one (ne_of_gt hz)
  have hn : 1+1/z = (z+1)/z := by field_simp
  unfold gammaError step
  rw [hr, Real.log_mul (ne_of_gt hz) (ne_of_gt hg), hn,
    Real.log_div (by linarith) (ne_of_gt hz)]
  ring

theorem upperError_strict_mono_step {z : ℝ} (hz : 0 < z) :
    gammaError z-stirlingUpper z < gammaError (z+1)-stirlingUpper (z+1) := by
  have h := stirlingUpper_step hz
  rw [← gammaError_step hz] at h
  linarith

end Schmidlin
