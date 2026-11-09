import HalfPlane
open Filter Topology
namespace ContactPilot
noncomputable section

/-- Every root, not just the minimal-height witness, tends uniformly to zero.
This supplies the localization missing from the half-plane contact predicate. -/
theorem R_roots_localize (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in 𝓝 0, ∀ w : ℂ, R x w = 0 → ‖w‖ < ε := by
  obtain ⟨u,v,hu,hv,_hu₀,_hv₀,hb⟩ := analytic_exhaustive_branches
  have roots := R_all_roots (hb.mono fun _ hx => hx.2.2)
  have cu : ContinuousAt (fun x : ℝ => ‖(x:ℂ)*u x‖) 0 :=
    (Complex.continuous_ofReal.continuousAt.mul
      (hu.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp))).norm
  have cv : ContinuousAt (fun x : ℝ => ‖(x:ℂ)*v x‖) 0 :=
    (Complex.continuous_ofReal.continuousAt.mul
      (hv.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp))).norm
  have bu : ∀ᶠ x : ℝ in 𝓝 0, ‖(x:ℂ)*u x‖ < ε :=
    cu.eventually_lt_const (by simpa using hε)
  have bv : ∀ᶠ x : ℝ in 𝓝 0, ‖(x:ℂ)*v x‖ < ε :=
    cv.eventually_lt_const (by simpa using hε)
  filter_upwards [(Complex.continuous_ofReal.tendsto (0:ℝ)).eventually
    (by simpa using roots), bu, bv] with x hx hux hvx
  intro w hw
  rcases (hx w).mp hw with rfl | rfl
  · exact hux
  · exact hvx

/-- Half-plane contact with an arbitrarily small prescribed root neighborhood.
The original lower constant 1/4 and upper constant 1 are preserved. -/
theorem half_plane_contact_six_localized (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x| → |x| < δ →
      (∀ w : ℂ, w.im < 0 → R x w = 0 →
        (1/4:ℝ)*|x|^6 ≤ |w.im|) ∧
      (∃ w : ℂ, ‖w‖ < ε ∧ w.im < 0 ∧ R x w = 0 ∧
        |w.im| ≤ |x|^6) := by
  obtain ⟨u,v,g,h,hu,hv,hg,hh,hu₀,hv₀,hg₀,hh₀,hb,_ho⟩ := concrete_orders_six_two
  have hgu := hb.mono fun _ hx => hx.2.2.1
  have hhv := hb.mono fun _ hx => hx.2.2.2
  have bounds := branch_bounds hg hh hg₀ hh₀ hgu hhv
  have roots := R_all_roots (hb.mono fun _ hx => hx.2.1)
  have rootsR : ∀ᶠ x : ℝ in 𝓝 0, ∀ w : ℂ,
      R x w = 0 ↔ w = (x:ℂ)*u x ∨ w = (x:ℂ)*v x :=
    (Complex.continuous_ofReal.tendsto (0:ℝ)).eventually (by simpa using roots)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp
    (bounds.and (rootsR.and (R_roots_localize ε hε)))
  refine ⟨δ,hδ,?_⟩
  intro x hx hxd
  obtain ⟨b,r,loc⟩ := hd (by simpa [Real.dist_eq] using hxd)
  obtain ⟨nu,_nv,bu,cu,_bv,_cv,bmin,_cmin⟩ := b hx
  constructor
  · intro w _hi hr
    rcases (r w).mp hr with rfl | rfl
    · exact bu
    · exact bmin.trans (min_le_right _ _)
  · have hr := (r ((x:ℂ)*u x)).mpr (Or.inl rfl)
    exact ⟨(x:ℂ)*u x,loc _ hr,nu,hr,cu⟩
end
end ContactPilot
