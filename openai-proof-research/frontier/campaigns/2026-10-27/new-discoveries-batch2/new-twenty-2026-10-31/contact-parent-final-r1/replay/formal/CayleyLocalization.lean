import CayleyRootBridge
open Filter Topology
namespace ContactPilot
noncomputable section

 theorem beta_norm_lt_one (y : ℂ) (hy : 0 < y.im) : ‖beta y‖ < 1 := by
  have hd := beta_denominator_ne y hy.le
  have hs : ‖1-Complex.I*y‖^2 - ‖1+Complex.I*y‖^2 = 4*y.im := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  have hn : ‖1+Complex.I*y‖ < ‖1-Complex.I*y‖ := by
    nlinarith [norm_nonneg (1+Complex.I*y),norm_nonneg (1-Complex.I*y)]
  simpa only [beta,norm_div] using (div_lt_one (norm_pos_iff.mpr hd)).mpr hn

 theorem beta_near_one (y : ℂ) (hy : ‖y‖ < 1/2) :
    ‖beta y - 1‖ ≤ 4*‖y‖ := by
  have hn : 1/2 ≤ ‖1-Complex.I*y‖ := by
    have h := norm_sub_norm_le (1:ℂ) (Complex.I*y)
    simp only [norm_one, norm_mul, Complex.norm_I, one_mul] at h
    linarith
  have hd : 1-Complex.I*y ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : beta y-1 = (2*Complex.I*y)/(1-Complex.I*y) := by
    unfold beta
    field_simp
    ring
  rw [he, norm_div]
  have hnum : ‖(2:ℂ)*Complex.I*y‖ = 2*‖y‖ := by norm_num [norm_mul]
  rw [hnum]
  apply (div_le_iff₀ (by linarith : 0 < ‖1-Complex.I*y‖)).mpr
  nlinarith [norm_nonneg y]

/-- Actual numerator roots are localized near 1 before being used as witnesses. -/
 theorem numerator_images_localize (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in 𝓝 0, ∀ u : ℂ, u.im < 0 → R x u = 0 →
      ‖beta (star u)‖ < 1 ∧ ‖beta (star u)-1‖ < ε := by
  filter_upwards [R_roots_localize (min (1/2) (ε/4)) (lt_min (by norm_num) (by positivity))]
    with x hx
  intro u hi hr
  have hn := hx u hr
  have hs : ‖star u‖ < 1/2 := by simpa using hn.trans_le (min_le_left _ _)
  have hεu : ‖star u‖ < ε/4 := by simpa using hn.trans_le (min_le_right _ _)
  refine ⟨beta_norm_lt_one _ (by simpa using neg_pos.mpr hi), ?_⟩
  exact (beta_near_one _ hs).trans_lt (by linarith)
end
end ContactPilot
