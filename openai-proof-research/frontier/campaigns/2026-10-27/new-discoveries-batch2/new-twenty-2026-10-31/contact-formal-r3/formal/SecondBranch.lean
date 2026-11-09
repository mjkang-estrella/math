import ExactOrders
open Filter Topology
namespace ContactPilot
noncomputable section

def H₃ (x : ℂ) : ℂ := 6 - 4*Complex.I - 15*x + 9*Complex.I*x^2

theorem residual_three (x : ℂ) :
    A x * (-3)^2 + B x * (-3) + C x = x * H₃ x := by
  unfold A B C H₃
  ring

theorem analytic_remainder_three {v : ℂ → ℂ} (hv : AnalyticAt ℂ v 0)
    (hv₀ : v 0 = -3)
    (heq : ∀ᶠ x in 𝓝 (0:ℂ), A x*v x^2+B x*v x+C x = 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = 3-2*Complex.I ∧
      ∀ᶠ x in 𝓝 (0:ℂ), v x = -3 + x*h x := by
  let d : ℂ → ℂ := fun x => A x*(v x-3)+B x
  have hd : AnalyticAt ℂ d 0 := by dsimp [d]; unfold A B; fun_prop
  have hd₀ : d 0 = -2 := by simp [d, A, B, hv₀]; ring
  let h : ℂ → ℂ := fun x => -H₃ x / d x
  have hn : d 0 ≠ 0 := by rw [hd₀]; norm_num
  refine ⟨h, ?_, ?_, ?_⟩
  · exact (show AnalyticAt ℂ (fun x => -H₃ x) 0 by unfold H₃; fun_prop).div hd hn
  · dsimp [h]; rw [hd₀]; unfold H₃; ring
  · filter_upwards [heq, hd.continuousAt.eventually_ne hn] with x hx hnx
    have hr := residual_three x
    have hdiff : (v x+3)*d x = -(x*H₃ x) := by
      dsimp [d]
      linear_combination hx - hr
    dsimp [h]
    field_simp
    linear_combination hdiff

theorem imaginary_order_two {v h : ℂ → ℂ} (hv : AnalyticAt ℂ v 0)
    (hh : AnalyticAt ℂ h 0)
    (hrem : ∀ᶠ x in 𝓝 (0:ℂ), v x = -3+x*h x)
    (hh₀ : h 0 = 3-2*Complex.I) :
    analyticOrderAt (fun x : ℝ => ((x:ℂ)*v x).im) 0 = (2:ℕ) := by
  have hreal : AnalyticAt ℝ (fun x : ℝ => ((x:ℂ)*v x).im) 0 := by
    exact (Complex.imCLM.analyticAt _).comp (((Complex.ofRealCLM.analyticAt _).mul
      ((hv.restrictScalars (𝕜 := ℝ)).comp_of_eq (Complex.ofRealCLM.analyticAt _) (by simp))))
  rw [hreal.analyticOrderAt_eq_natCast]
  refine ⟨fun x : ℝ => (h x).im, ?_, ?_, ?_⟩
  · exact (Complex.imCLM.analyticAt _).comp
      ((hh.restrictScalars (𝕜 := ℝ)).comp_of_eq (Complex.ofRealCLM.analyticAt _) (by simp))
  · simp [hh₀]
  · filter_upwards [(Complex.continuous_ofReal.tendsto (0:ℝ)).eventually (by simpa using hrem)] with x hx
    simp [hx, Complex.mul_im]
    ring

/-- Both orders refer to branches of the same exhaustive analytic factorization. -/
theorem concrete_orders_six_two :
    ∃ u v g h : ℂ → ℂ,
      AnalyticAt ℂ u 0 ∧ AnalyticAt ℂ v 0 ∧
      AnalyticAt ℂ g 0 ∧ AnalyticAt ℂ h 0 ∧
      u 0 = -1 ∧ v 0 = -3 ∧ g 0 = 17/4-Complex.I/2 ∧ h 0 = 3-2*Complex.I ∧
      (∀ᶠ x in 𝓝 (0:ℂ), A x ≠ 0 ∧
        (∀ t : ℂ, A x*t^2+B x*t+C x = 0 ↔ t = u x ∨ t = v x) ∧
        u x = P x+x^5*g x ∧ v x = -3+x*h x) ∧
      analyticOrderAt (fun x : ℝ => ((x:ℂ)*u x).im) 0 = (6:ℕ) ∧
      analyticOrderAt (fun x : ℝ => ((x:ℂ)*v x).im) 0 = (2:ℕ) := by
  obtain ⟨u, v, hu, hv, hu₀, hv₀, hb⟩ := analytic_exhaustive_branches
  have hequ : ∀ᶠ x in 𝓝 (0:ℂ), A x*u x^2+B x*u x+C x = 0 := by
    filter_upwards [hb] with x hx
    exact (hx.2.2 (u x)).mpr (Or.inl rfl)
  have heqv : ∀ᶠ x in 𝓝 (0:ℂ), A x*v x^2+B x*v x+C x = 0 := by
    filter_upwards [hb] with x hx
    exact (hx.2.2 (v x)).mpr (Or.inr rfl)
  obtain ⟨g, hg, hg₀, hgu⟩ := analytic_remainder hu hu₀ hequ
  obtain ⟨h, hh, hh₀, hhv⟩ := analytic_remainder_three hv hv₀ heqv
  refine ⟨u, v, g, h, hu, hv, hg, hh, hu₀, hv₀, hg₀, hh₀, ?_,
    imaginary_order_six hu hg hgu hg₀, imaginary_order_two hv hh hhv hh₀⟩
  filter_upwards [hb, hgu, hhv] with x hx hux hvx
  exact ⟨hx.1, hx.2.2, hux, hvx⟩
end
end ContactPilot
