import QuadraticBranches
open Filter Topology
namespace ContactPilot
noncomputable section

/-- A real polynomial approximation to the slope -1 branch, before the first
nonreal coefficient. This is not an order theorem. -/
def P (x : ℂ) : ℂ := -1-x-x^2-x^3/2+x^4

def H (x : ℂ) : ℂ := (-17/2+Complex.I) + (-11/4+4*Complex.I)*x +
  (1+7*Complex.I/4)*x^2 + (9/2)*x^3 + (2-11*Complex.I/4)*x^4 +
  (-2-Complex.I)*x^5 + Complex.I*x^6

theorem residual_identity (x : ℂ) :
    A x * P x ^ 2 + B x * P x + C x = x^5 * H x := by
  unfold A B C P H
  ring

/-- Analytic remainder extraction by a nonvanishing divided difference. This
avoids treating formal polynomial jets as convergent branch expansions. -/
theorem analytic_remainder {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0)
    (hu₀ : u 0 = -1)
    (heq : ∀ᶠ x in 𝓝 (0:ℂ), A x*u x^2+B x*u x+C x = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 17/4-Complex.I/2 ∧
      ∀ᶠ x in 𝓝 (0:ℂ), u x = P x + x^5*g x := by
  let v : ℂ → ℂ := fun x => A x*(u x+P x)+B x
  have hv : AnalyticAt ℂ v 0 := by dsimp [v]; unfold A B P; fun_prop
  have hv₀ : v 0 = 2 := by simp [v, A, B, P, hu₀]; ring
  let g : ℂ → ℂ := fun x => -H x / v x
  have hn : v 0 ≠ 0 := by rw [hv₀]; norm_num
  refine ⟨g, ?_, ?_, ?_⟩
  · exact (show AnalyticAt ℂ (fun x => -H x) 0 by unfold H; fun_prop).div hv hn
  · dsimp [g]; rw [hv₀]; unfold H; ring
  · filter_upwards [heq, hv.continuousAt.eventually_ne hn] with x hx hnx
    have hr := residual_identity x
    have hdiff : (u x-P x)*v x = -(x^5*H x) := by
      dsimp [v]
      linear_combination hx - hr
    dsimp [g]
    field_simp
    linear_combination hdiff
end
end ContactPilot

namespace ContactPilot
/-- Unconditional convergence information for the concrete slope -1 branch.
It is deliberately not labeled a contact-order result. -/
theorem concrete_analytic_remainder :
    ∃ u g : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ AnalyticAt ℂ g 0 ∧
      u 0 = -1 ∧ g 0 = 17/4-Complex.I/2 ∧
      (∀ᶠ x in 𝓝 (0:ℂ), A x*u x^2+B x*u x+C x = 0) ∧
      (∀ᶠ x in 𝓝 (0:ℂ), u x = P x + x^5*g x) := by
  obtain ⟨u, v, hu, _, hu₀, _, hbranches⟩ := analytic_exhaustive_branches
  have heq : ∀ᶠ x in 𝓝 (0:ℂ), A x*u x^2+B x*u x+C x = 0 := by
    filter_upwards [hbranches] with x hx
    exact (hx.2.2 (u x)).mpr (Or.inl rfl)
  obtain ⟨g, hg, hg₀, hrem⟩ := analytic_remainder hu hu₀ heq
  exact ⟨u, g, hu, hg, hu₀, hg₀, heq, hrem⟩
end ContactPilot

namespace ContactPilot
theorem imaginary_order_six {u g : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hg : AnalyticAt ℂ g 0)
    (hrem : ∀ᶠ x in 𝓝 (0:ℂ), u x = P x+x^5*g x)
    (hg₀ : g 0 = 17/4-Complex.I/2) :
    analyticOrderAt (fun x : ℝ => ((x:ℂ)*u x).im) 0 = (6:ℕ) := by
  have hreal : AnalyticAt ℝ (fun x : ℝ => ((x:ℂ)*u x).im) 0 := by
    exact (Complex.imCLM.analyticAt _).comp (((Complex.ofRealCLM.analyticAt _).mul
      ((hu.restrictScalars (𝕜 := ℝ)).comp_of_eq (Complex.ofRealCLM.analyticAt _) (by simp))))
  rw [hreal.analyticOrderAt_eq_natCast]
  refine ⟨fun x : ℝ => (g x).im, ?_, ?_, ?_⟩
  · exact (Complex.imCLM.analyticAt _).comp
      ((hg.restrictScalars (𝕜 := ℝ)).comp_of_eq (Complex.ofRealCLM.analyticAt _) (by simp))
  · simp [hg₀]
  · filter_upwards [(Complex.continuous_ofReal.tendsto (0:ℝ)).eventually (by simpa using hrem)] with x hx
    simp [hx, P, Complex.mul_im, ← Complex.ofReal_pow]
    ring

end ContactPilot

namespace ContactPilot
/-- A genuine exact-order statement for one concrete analytic root, with an
analytic remainder. The second branch and full zero-set contact are not asserted. -/
theorem concrete_order_six : ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 = -1 ∧
    (∀ᶠ x in 𝓝 (0:ℂ), A x*u x^2+B x*u x+C x = 0) ∧
    analyticOrderAt (fun x : ℝ => ((x:ℂ)*u x).im) 0 = (6:ℕ) := by
  obtain ⟨u, g, hu, hg, hu₀, hg₀, heq, hrem⟩ := concrete_analytic_remainder
  exact ⟨u, hu, hu₀, heq, imaginary_order_six hu hg hrem hg₀⟩
end ContactPilot
