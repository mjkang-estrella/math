import CayleyHeight
open Filter Topology
namespace ContactPilot
noncomputable section

 theorem beta_betaInv (v : ℂ) (hv : 1+v ≠ 0) : beta (betaInv v) = v := by
  unfold beta betaInv
  field_simp
  ring_nf
  norm_num [Complex.I_sq]; ring

 theorem betaInv_near_zero (v : ℂ) (hv : ‖v-1‖ < 1/2) :
    ‖betaInv v‖ < 1/2 := by
  have hd : 1 ≤ ‖1+v‖ := by
    have h := norm_sub_norm_le (2:ℂ) (1-v)
    have he : (2:ℂ)-(1-v) = 1+v := by ring
    rw [he] at h
    norm_num only [show ‖(2:ℂ)‖ = (2:ℝ) by norm_num] at h
    rw [norm_sub_rev] at h
    linarith
  have he : ‖betaInv v‖ = ‖v-1‖/‖1+v‖ := by
    simp [betaInv,norm_sub_rev]
  rw [he]
  apply (div_lt_iff₀ (by linarith : 0 < ‖1+v‖)).mpr
  linarith

/-- Both contact comparisons in the real Cayley parameter, with fixed constants. -/
 theorem parameterized_contact_six :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x| → |x| < δ →
      (∀ v : ℂ, ‖v‖ < 1 → ‖v-1‖ < 1/2 →
        eval₂ bidiskNumerator (-beta (x:ℂ)) v = 0 →
        (1/8:ℝ)*|x|^6 ≤ 1-‖v‖) ∧
      (∃ v : ℂ, ‖v‖ < 1 ∧ ‖v-1‖ < 1/2 ∧
        eval₂ bidiskNumerator (-beta (x:ℂ)) v = 0 ∧
        1-‖v‖ ≤ 16*|x|^6) := by
  obtain ⟨δ,hδ,hd⟩ := half_plane_contact_six_localized (1/8) (by norm_num)
  refine ⟨δ,hδ,?_⟩
  intro x hx hxd
  have hx0 : x ≠ 0 := abs_pos.mp hx
  obtain ⟨lower,upper⟩ := hd x hx hxd
  constructor
  · intro v hv hloc hroot
    have hp := betaInv_im_pos v hv
    have hn := betaInv_near_zero v hloc
    have hr := (numerator_root_iff x hx0 v (disk_one_add_ne_zero v hv)).mp hroot
    have hl := lower (star (betaInv v)) (by simpa using neg_neg_of_pos hp) hr
    have hl' : (1/4:ℝ)*|x|^6 ≤ (betaInv v).im := by simpa [abs_of_pos hp] using hl
    have hh := (beta_height_comparison _ hp hn).1
    rw [beta_betaInv v (disk_one_add_ne_zero v hv)] at hh
    linarith
  · obtain ⟨u,hu,hi,hr,hupper⟩ := upper
    have hs : ‖star u‖ < 1/2 := by simpa using hu.trans (by norm_num : (1/8:ℝ)<1/2)
    have hp : 0 < (star u).im := by simpa using neg_pos.mpr hi
    have hn := beta_norm_lt_one _ hp
    have hnear := beta_near_one (star u) hs
    have hheight := (beta_height_comparison _ hp hs).2
    refine ⟨beta (star u),hn,?_,pole_root_maps_to_numerator x hx0 u hi hr,?_⟩
    · simp only [norm_star] at hnear
      linarith
    · have him : (star u).im = |u.im| := by simp [abs_of_neg hi]
      rw [him] at hheight
      linarith
end
end ContactPilot
