import CircleChart
namespace ContactPilot
noncomputable section

 theorem bidisk_contact_six :
    HasZeroSetContact (eval₂ bidiskNumerator) (-1) 1 6 := by
  obtain ⟨δ,hδ,hd⟩ := parameterized_contact_six
  refine ⟨by norm_num,by norm_num,bidisk_boundary_zero.1,
    min δ (1/2),1/2,1/512,16,lt_min hδ (by norm_num),by norm_num,
    by norm_num,by norm_num,?_⟩
  intro z hz hp hs
  have hpos : 0 < ‖z+1‖ := by simpa using hp
  have hsmall : ‖z+1‖ < 1/2 := by simpa using hs.trans_le (min_le_right _ _)
  have hδz : ‖z+1‖ < δ := by simpa using hs.trans_le (min_le_left _ _)
  obtain ⟨hx,hl,hu⟩ := circleChart_bounds z hz hpos hsmall
  have hne : 1-z ≠ 0 := by
    intro he
    have ez : z = 1 := by linear_combination -he
    norm_num [ez] at hsmall
  have he : -beta ((circleChart z).re:ℂ) = z := by
    rw [circleChart_real z hz,circleChart_inverse z hne]
  obtain ⟨lower,upper⟩ := hd (circleChart z).re hx (hu.trans_lt hδz)
  rw [he] at lower upper
  constructor
  · intro v hv hnear hroot
    have hb := lower v hv hnear hroot
    have hp6 : (‖z+1‖/2)^6 ≤ |(circleChart z).re|^6 :=
      pow_le_pow_left₀ (by positivity) hl 6
    have ht : (1/512:ℝ)*‖z+1‖^6 ≤ 1-‖v‖ := by
      nlinarith
    simpa using ht
  · obtain ⟨v,hv,hn,hr,hb⟩ := upper
    refine ⟨v,hv,hn,hr,?_⟩
    have hp6 := pow_le_pow_left₀ (abs_nonneg (circleChart z).re) hu 6
    have ht : 1-‖v‖ ≤ 16*‖z+1‖^6 := by linarith
    simpa using ht
end
end ContactPilot
