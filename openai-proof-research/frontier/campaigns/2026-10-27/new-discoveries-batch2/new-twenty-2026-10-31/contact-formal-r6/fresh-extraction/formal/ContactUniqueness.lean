import SourceContactLocal
open Filter Topology
namespace ContactPilot
noncomputable section

/-- The unit circle has punctured points arbitrarily close to every unit point. -/
theorem circle_punctured_small (τ : ℂ) (hτ : ‖τ‖ = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ 0 < ‖z-τ‖ ∧ ‖z-τ‖ < ε := by
  have cb : ContinuousAt (fun x : ℝ => beta (x:ℂ)) 0 := by
    unfold beta
    fun_prop (disch := norm_num)
  have ct : ContinuousAt (fun x : ℝ => ‖τ * beta (x:ℂ)-τ‖) 0 := by
    exact ((continuousAt_const.mul cb).sub continuousAt_const).norm
  have ev : ∀ᶠ x : ℝ in 𝓝 0, ‖τ * beta (x:ℂ)-τ‖ < ε :=
    ct.eventually_lt_const (by simpa [beta] using hε)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp ev
  obtain ⟨x,hx,hxs⟩ := exists_between (lt_min hδ (by norm_num : (0:ℝ)<1/2))
  have he : ‖τ * beta (x:ℂ)-τ‖ = ‖-beta (x:ℂ)+1‖ := by
    rw [show τ * beta (x:ℂ)-τ = τ * (beta (x:ℂ)-1) by ring, norm_mul,hτ,one_mul]
    rw [show -beta (x:ℂ)+1 = -(beta (x:ℂ)-1) by ring,norm_neg]
  refine ⟨τ * beta (x:ℂ),by simp [hτ,beta_real_norm],?_,?_⟩
  · rw [he]
    exact lt_of_lt_of_le (by simpa [abs_of_pos hx] using hx)
      (beta_real_displacement x (by simpa [abs_of_pos hx] using hxs.trans_le (min_le_right _ _))).1
  · exact hd (by simpa [Real.dist_eq,abs_of_pos hx] using hxs.trans_le (min_le_left _ _))

 theorem local_contact_order_le {q : ℂ → ℂ → ℂ} {τ₁ τ₂ : ℂ} {K₁ K₂ : ℕ}
    (h₁ : HasLocalZeroSetContact q τ₁ τ₂ K₁)
    (h₂ : HasLocalZeroSetContact q τ₁ τ₂ K₂) : K₂ ≤ K₁ := by
  by_contra hn
  have hk : K₁ < K₂ := Nat.lt_of_not_ge hn
  obtain ⟨hτ,_,_,c₁,C₁,r₁,hc₁,_hC₁,hr₁,⟨d₁,hd₁,lower⟩,_⟩ := h₁
  obtain ⟨_,_,_,c₂,C₂,r₂,_hc₂,hC₂,hr₂,_,upper⟩ := h₂
  obtain ⟨d₂,hd₂,upper⟩ := upper (min r₁ r₂) (lt_min hr₁ hr₂) (min_le_right _ _)
  have ev : ∀ᶠ t : ℝ in 𝓝 0, C₂ * t^(K₂-K₁) < c₁ :=
    (show ContinuousAt (fun t : ℝ => C₂*t^(K₂-K₁)) 0 by fun_prop).eventually_lt_const
      (by simpa [Nat.ne_of_gt (Nat.sub_pos_of_lt hk)] using hc₁)
  obtain ⟨e,he,hes⟩ := Metric.eventually_nhds_iff.mp ev
  obtain ⟨z,hz,hpos,hsmall⟩ := circle_punctured_small τ₁ hτ (min e (min d₁ d₂))
    (lt_min he (lt_min hd₁ hd₂))
  obtain ⟨v,hv,hr,root,up⟩ := upper z hz hpos
    (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have lo := lower z hz hpos
    (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))) v hv
    (hr.trans_le (min_le_left _ _)) root
  have hs := hes (y := ‖z-τ₁‖) (by simpa [Real.dist_eq,abs_of_pos hpos] using
    (hsmall.trans_le (min_le_left _ _)))
  have hp := mul_lt_mul_of_pos_right hs (pow_pos hpos K₁)
  have heq : C₂ * ‖z-τ₁‖^(K₂-K₁) * ‖z-τ₁‖^K₁ = C₂ * ‖z-τ₁‖^K₂ := by
    rw [mul_assoc,← pow_add,Nat.sub_add_cancel hk.le]
  rw [heq] at hp
  linarith

 theorem local_contact_unique {q : ℂ → ℂ → ℂ} {τ₁ τ₂ : ℂ} {K₁ K₂ : ℕ}
    (h₁ : HasLocalZeroSetContact q τ₁ τ₂ K₁)
    (h₂ : HasLocalZeroSetContact q τ₁ τ₂ K₂) : K₁ = K₂ :=
  Nat.le_antisymm (local_contact_order_le h₂ h₁) (local_contact_order_le h₁ h₂)
end
end ContactPilot
