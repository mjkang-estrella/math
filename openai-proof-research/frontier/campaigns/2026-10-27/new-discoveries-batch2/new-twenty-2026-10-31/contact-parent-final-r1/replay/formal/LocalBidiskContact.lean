import SourceContactLocal
import ParameterizedContact
open Filter Topology
namespace ContactPilot
noncomputable section
/-- Both contact comparisons in the real Cayley parameter, with fixed constants. -/
 theorem parameterized_contact_six_localized (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x| → |x| < δ →
      (∀ v : ℂ, ‖v‖ < 1 → ‖v-1‖ < 1/2 →
        eval₂ bidiskNumerator (-beta (x:ℂ)) v = 0 →
        (1/8:ℝ)*|x|^6 ≤ 1-‖v‖) ∧
      (∃ v : ℂ, ‖v‖ < 1 ∧ ‖v-1‖ < ε ∧
        eval₂ bidiskNumerator (-beta (x:ℂ)) v = 0 ∧
        1-‖v‖ ≤ 16*|x|^6) := by
  obtain ⟨δ,hδ,hd⟩ := half_plane_contact_six_localized (min (1/8) (ε/4)) (lt_min (by norm_num) (by positivity))
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
    have hs : ‖star u‖ < 1/2 := by simpa using (hu.trans_le (min_le_left _ _)).trans (by norm_num : (1/8:ℝ)<1/2)
    have hp : 0 < (star u).im := by simpa using neg_pos.mpr hi
    have hn := beta_norm_lt_one _ hp
    have hnear := beta_near_one (star u) hs
    have hheight := (beta_height_comparison _ hp hs).2
    refine ⟨beta (star u),hn,?_,pole_root_maps_to_numerator x hx0 u hi hr,?_⟩
    · simp only [norm_star] at hnear
      have huε := hu.trans_le (min_le_right (1/8:ℝ) (ε/4))
      linarith
    · have him : (star u).im = |u.im| := by simp [abs_of_neg hi]
      rw [him] at hheight
      linarith

 theorem bidisk_local_contact_six :
    HasLocalZeroSetContact (eval₂ bidiskNumerator) (-1) 1 6 := by
  obtain ⟨_,_,_,d,r,c,C,hd,hr,hc,hC,hcontact⟩ := bidisk_contact_six
  refine ⟨by norm_num,by norm_num,bidisk_boundary_zero.1,c,16,r,hc,by norm_num,hr,
    ⟨d,hd,fun z hz hp hs => (hcontact z hz hp hs).1⟩,?_⟩
  intro ρ hρ _hρr
  obtain ⟨δ,hδ,hd⟩ := parameterized_contact_six_localized ρ hρ
  refine ⟨min δ (1/2),lt_min hδ (by norm_num),?_⟩
  intro z hz hp hs
  have hpos : 0 < ‖z+1‖ := by simpa using hp
  have hsmall : ‖z+1‖ < 1/2 := by simpa using hs.trans_le (min_le_right _ _)
  have hδz : ‖z+1‖ < δ := by simpa using hs.trans_le (min_le_left _ _)
  obtain ⟨hx,_hl,hu⟩ := circleChart_bounds z hz hpos hsmall
  have hne : 1-z ≠ 0 := by
    intro he
    have ez : z = 1 := by linear_combination -he
    norm_num [ez] at hsmall
  have he : -beta ((circleChart z).re:ℂ) = z := by
    rw [circleChart_real z hz,circleChart_inverse z hne]
  obtain ⟨_lower,upper⟩ := hd (circleChart z).re hx (hu.trans_lt hδz)
  rw [he] at upper
  obtain ⟨v,hv,hn,hr,hb⟩ := upper
  refine ⟨v,hv,hn,hr,?_⟩
  have hp6 := pow_le_pow_left₀ (abs_nonneg (circleChart z).re) hu 6
  have ht : 1-‖v‖ ≤ 16*‖z+1‖^6 := by linarith
  simpa using ht
end
end ContactPilot
