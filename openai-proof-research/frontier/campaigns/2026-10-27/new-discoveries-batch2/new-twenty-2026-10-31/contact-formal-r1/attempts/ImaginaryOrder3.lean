import ExactOrders
open Filter Topology ContactPilot
-- Failed P3 bridge probe; excluded from the verified source modules.
-- Complex analyticity cannot be used directly for the imaginary part.
example {u g : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hg : AnalyticAt ℂ g 0)
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
