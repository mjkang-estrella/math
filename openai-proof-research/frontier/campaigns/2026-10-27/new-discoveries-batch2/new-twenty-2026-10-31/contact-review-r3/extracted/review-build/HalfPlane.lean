import BranchBounds
open Filter Topology
namespace ContactPilot
noncomputable section

/-- Cleared polynomial Q-iN in the x=-1/z chart. -/
def R (x w : ℂ) : ℂ := A x*w^2 + x*B x*w + x^2*C x

theorem R_expanded (x w : ℂ) : R x w =
    (1-Complex.I*x-2*x^2+Complex.I*x^3)*w^2 +
    (4*x-(2+2*Complex.I)*x^2-x^3)*w+3*x^2-Complex.I*x^3 := by
  unfold R A B C
  ring

theorem R_zero (w : ℂ) : R 0 w = 0 ↔ w = 0 := by
  simp [R, A, pow_eq_zero_iff]

theorem R_normalized (x t : ℂ) :
    R x (x*t) = x^2*(A x*t^2+B x*t+C x) := by unfold R; ring

/-- Exhaustive transfer, with zero and nonzero parameters explicitly separated. -/
theorem R_all_roots {u v : ℂ → ℂ}
    (hb : ∀ᶠ x in 𝓝 (0:ℂ),
      ∀ t : ℂ, A x*t^2+B x*t+C x = 0 ↔ t = u x ∨ t = v x) :
    ∀ᶠ x in 𝓝 (0:ℂ), ∀ w : ℂ,
      R x w = 0 ↔ w = x*u x ∨ w = x*v x := by
  filter_upwards [hb] with x hx
  intro w
  by_cases h0 : x = 0
  · subst x; simp [R_zero]
  have hn : x^2 ≠ 0 := pow_ne_zero _ h0
  have hw : x*(w/x) = w := mul_div_cancel₀ w h0
  constructor
  · intro hr
    have hF : A x*(w/x)^2+B x*(w/x)+C x = 0 := by
      have eqn := R_normalized x (w/x)
      rw [hw, hr] at eqn
      exact (mul_eq_zero.mp eqn.symm).resolve_left hn
    rcases (hx (w/x)).mp hF with hu | hv
    · exact Or.inl (by rw [← hw, hu])
    · exact Or.inr (by rw [← hw, hv])
  · rintro (rfl | rfl)
    · rw [R_normalized, (hx (u x)).mpr (Or.inl rfl), mul_zero]
    · rw [R_normalized, (hx (v x)).mpr (Or.inr rfl), mul_zero]

/-- Contact six for the actual complete zero set of the cleared polynomial.
The graph-resolvent and reduced bidisk representation are separate obligations. -/
theorem half_plane_contact_six : HasHalfPlaneContact R 6 := by
  obtain ⟨u,v,g,h,hu,hv,hg,hh,hu₀,hv₀,hg₀,hh₀,hb,_ho⟩ := concrete_orders_six_two
  have hgu : ∀ᶠ x in 𝓝 (0:ℂ), u x = P x+x^5*g x := hb.mono fun _ hx => hx.2.2.1
  have hhv : ∀ᶠ x in 𝓝 (0:ℂ), v x = -3+x*h x := hb.mono fun _ hx => hx.2.2.2
  have hbound := branch_bounds hg hh hg₀ hh₀ hgu hhv
  have hall := R_all_roots (hb.mono fun _ hx => hx.2.1)
  have hallR : ∀ᶠ x : ℝ in 𝓝 0, ∀ w : ℂ,
      R x w = 0 ↔ w = (x:ℂ)*u x ∨ w = (x:ℂ)*v x :=
    (Complex.continuous_ofReal.tendsto (0:ℝ)).eventually (by simpa using hall)
  have hnorm : ∀ᶠ x : ℝ in 𝓝 0, ‖(x:ℂ)*u x‖ < 1 := by
    have ct : ContinuousAt (fun x : ℝ => ‖(x:ℂ)*u x‖) 0 :=
      (Complex.continuous_ofReal.continuousAt.mul
        (hu.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp))).norm
    exact ct.eventually_lt_const (by simp)
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp (hbound.and (hallR.and hnorm))
  refine ⟨?_, δ, 1, 1/4, 1, hδ, by norm_num, by norm_num, by norm_num, ?_⟩
  · simp [R]
  · intro x hx hxd
    obtain ⟨bounds, roots, normu⟩ := hd (by simpa [Real.dist_eq] using hxd)
    obtain ⟨nu,nv,bu,cu,bv,_cv,_bmin,_cmin⟩ := bounds hx
    constructor
    · intro w _hw _hi hr
      rcases (roots w).mp hr with rfl | rfl
      · exact bu
      · exact _bmin.trans (min_le_right _ _)
    · exact ⟨(x:ℂ)*u x, normu, nu, (roots _).mpr (Or.inl rfl), by simpa using cu⟩
end
end ContactPilot
