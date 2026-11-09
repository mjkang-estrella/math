import ParameterizedContact
namespace ContactPilot
noncomputable section

def circleChart (z : ℂ) : ℂ := Complex.I*(1+z)/(1-z)

 theorem circleChart_im (z : ℂ) :
    (circleChart z).im = (1-Complex.normSq z)/Complex.normSq (1-z) := by
  simp [circleChart,Complex.div_im,Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  ring

 theorem circleChart_real (z : ℂ) (hz : ‖z‖ = 1) :
    ((circleChart z).re:ℂ) = circleChart z := by
  have hi : (circleChart z).im = 0 := by
    rw [circleChart_im,Complex.normSq_eq_norm_sq,hz]
    norm_num
  apply Complex.ext <;> simp [hi]

 theorem circleChart_inverse (z : ℂ) (hz : 1-z ≠ 0) :
    -beta (circleChart z) = z := by
  unfold circleChart beta
  field_simp
  ring_nf
  norm_num [Complex.I_sq]; ring

/-- Uniform chart bounds on the unit circle near -1. -/
 theorem circleChart_bounds (z : ℂ) (hz : ‖z‖ = 1)
    (hpos : 0 < ‖z+1‖) (hsmall : ‖z+1‖ < 1/2) :
    0 < |(circleChart z).re| ∧
      ‖z+1‖/2 ≤ |(circleChart z).re| ∧
      |(circleChart z).re| ≤ ‖z+1‖ := by
  have hdL : 1 ≤ ‖1-z‖ := by
    have h := norm_sub_norm_le (2:ℂ) (z+1)
    have he : (2:ℂ)-(z+1) = 1-z := by ring
    rw [he] at h
    norm_num only [show ‖(2:ℂ)‖ = (2:ℝ) by norm_num] at h
    linarith
  have hdU : ‖1-z‖ ≤ 2 := by
    have h := norm_sub_le (1:ℂ) z
    simpa only [norm_one,hz,show (1:ℝ)+1=2 by norm_num] using h
  have hn : |(circleChart z).re| = ‖z+1‖/‖1-z‖ := by
    have he := congrArg norm (circleChart_real z hz)
    simp only [Complex.norm_real,Real.norm_eq_abs] at he
    rw [he]
    simp [circleChart,add_comm]
  rw [hn]
  have hd : 0 < ‖1-z‖ := by linarith
  refine ⟨div_pos hpos hd,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    nlinarith
end
end ContactPilot
