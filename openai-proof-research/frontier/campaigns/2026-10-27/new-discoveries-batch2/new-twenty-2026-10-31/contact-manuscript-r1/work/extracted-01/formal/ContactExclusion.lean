import BidiskContact
open Filter Topology
namespace ContactPilot
noncomputable section

 theorem beta_real_norm (x : ℝ) : ‖beta (x:ℂ)‖ = 1 := by
  have hd := beta_denominator_ne (x:ℂ) (by simp)
  have he : ‖1+Complex.I*(x:ℂ)‖ = ‖1-Complex.I*(x:ℂ)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  simp only [beta,norm_div,he,div_self (norm_ne_zero_iff.mpr hd)]

 theorem beta_real_displacement (x : ℝ) (hx : |x| < 1/2) :
    |x| ≤ ‖-beta (x:ℂ)+1‖ ∧ ‖-beta (x:ℂ)+1‖ ≤ 4*|x| := by
  have hd := beta_denominator_ne (x:ℂ) (by simp)
  have he : -beta (x:ℂ)+1 = (-2*Complex.I*(x:ℂ))/(1-Complex.I*(x:ℂ)) := by
    unfold beta
    field_simp
    ring
  have hn : ‖-beta (x:ℂ)+1‖ = 2*|x|/‖1-Complex.I*(x:ℂ)‖ := by
    rw [he,norm_div]
    norm_num [norm_mul]
  have hu : ‖1-Complex.I*(x:ℂ)‖ ≤ 2 := by
    have h := norm_sub_le (1:ℂ) (Complex.I*(x:ℂ))
    simp only [norm_one,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at h
    linarith
  constructor
  · rw [hn]
    apply (le_div_iff₀ (norm_pos_iff.mpr hd)).mpr
    nlinarith [abs_nonneg x]
  · have h := beta_near_one (x:ℂ) (by simpa using hx)
    have he' : -beta (x:ℂ)+1 = -(beta (x:ℂ)-1) := by ring
    rw [he',norm_neg]
    simpa only [Complex.norm_real,Real.norm_eq_abs] using h

/-- The predicted contact 2 is incompatible with the actual two-sided estimates.
The sixth-order witness is localized inside the asserted contact-2 neighborhood. -/
theorem bidisk_not_contact_two :
    ¬ HasZeroSetContact (eval₂ bidiskNumerator) (-1) 1 2 := by
  rintro ⟨_,_,_,δ,ρ,c,C,hδ,hρ,hc,_hC,hcontact⟩
  obtain ⟨d,hd,hhalf⟩ := half_plane_contact_six_localized (1/8) (by norm_num)
  have esmall : ∀ᶠ x : ℝ in 𝓝 0, |x| < min d (1/2) :=
    (show ContinuousAt (fun x : ℝ => |x|) 0 by fun_prop).eventually_lt_const
      (by simpa using lt_min hd (by norm_num : (0:ℝ)<1/2))
  have edelta : ∀ᶠ x : ℝ in 𝓝 0, 4*|x| < δ :=
    (show ContinuousAt (fun x : ℝ => 4*|x|) 0 by fun_prop).eventually_lt_const (by simpa using hδ)
  have epow : ∀ᶠ x : ℝ in 𝓝 0, 16*x^4 < c :=
    (show ContinuousAt (fun x : ℝ => 16*x^4) 0 by fun_prop).eventually_lt_const (by simpa using hc)
  obtain ⟨η,hη,he⟩ := Metric.eventually_nhds_iff.mp
    (esmall.and (edelta.and (epow.and (numerator_images_localize ρ hρ))))
  obtain ⟨x,hx,hxη⟩ := exists_between hη
  obtain ⟨hsmall,hdel,hpow,hloc⟩ := he (y := x) (by simpa [Real.dist_eq,abs_of_pos hx] using hxη)
  have hxd : |x| < d := hsmall.trans_le (min_le_left _ _)
  have hxhalf : |x| < 1/2 := hsmall.trans_le (min_le_right _ _)
  obtain ⟨u,hu,hi,hr,hupper⟩ := (hhalf x (by simpa [abs_of_pos hx] using hx) hxd).2
  have himg := hloc u hi hr
  have hroot := pole_root_maps_to_numerator x (ne_of_gt hx) u hi hr
  have hdisp := beta_real_displacement x hxhalf
  have hzpos : 0 < ‖-beta (x:ℂ)+1‖ := lt_of_lt_of_le (by simpa [abs_of_pos hx] using hx) hdisp.1
  have hzsmall : ‖-beta (x:ℂ)+1‖ < δ := hdisp.2.trans_lt hdel
  have hlow := (hcontact (-beta (x:ℂ)) (by simp [beta_real_norm])
    (by simpa using hzpos) (by simpa using hzsmall)).1 _ himg.1 himg.2 hroot
  have hp : 0 < (star u).im := by simpa using neg_pos.mpr hi
  have hnorm : ‖star u‖ < 1/2 := by simpa using hu.trans (by norm_num : (1/8:ℝ)<1/2)
  have hh := (beta_height_comparison _ hp hnorm).2
  have him : (star u).im = |u.im| := by simp [abs_of_neg hi]
  rw [him] at hh
  have hle : c*x^2 ≤ 1-‖beta (star u)‖ := by
    have hdx : x ≤ ‖-beta (x:ℂ)+1‖ := by simpa [abs_of_pos hx] using hdisp.1
    have hs : x^2 ≤ ‖-beta (x:ℂ)+1‖^2 := by nlinarith [norm_nonneg (-beta (x:ℂ)+1)]
    have heq : ‖-beta (x:ℂ)-(-1)‖ = ‖-beta (x:ℂ)+1‖ := by congr 1; ring
    rw [heq] at hlow
    nlinarith
  have hhi : 1-‖beta (star u)‖ ≤ 16*x^6 := by
    rw [abs_of_pos hx] at hupper
    linarith
  have hcontr := mul_lt_mul_of_pos_right hpow (sq_pos_of_pos hx)
  nlinarith
end
end ContactPilot
