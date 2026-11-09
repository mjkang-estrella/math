import KernelConcavity

set_option autoImplicit false

noncomputable section
open Set

namespace ArcsinhPositive

theorem sourceIntegrand_continuousOn {p x : ℝ} (hp : 0 < p) :
    ContinuousOn (sourceIntegrand p) (Icc 0 x) := by
  unfold sourceIntegrand
  apply ContinuousOn.rpow_const
    (continuousOn_const.add (continuousOn_id.rpow_const (fun _ _ ↦ Or.inr hp.le)))
  intro t ht
  apply Or.inl
  dsimp
  exact ne_of_gt (by linarith [Real.rpow_nonneg ht.1 p])

theorem sourceArcsinh_strictConcaveOn {x : ℝ} (hx : 0 < x) :
    StrictConcaveOn ℝ (Ioi (Real.log 2 / 2)) (fun p ↦ sourceArcsinh p x) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro p₀ hp₀ p₁ hp₁ hne a b ha hb hab
  have hth : 0 < Real.log 2 / 2 := by positivity
  have hp₀0 : 0 < p₀ := lt_trans hth hp₀
  have hp₁0 : 0 < p₁ := lt_trans hth hp₁
  have hM : Real.log 2 / 2 < a * p₀ + b * p₁ := by
    have h0 := mul_pos ha (sub_pos.mpr hp₀)
    have h1 := mul_pos hb (sub_pos.mpr hp₁)
    nlinarith
  have hM0 : 0 < a * p₀ + b * p₁ := lt_trans hth hM
  have hC₀ := sourceIntegrand_continuousOn (x := x) hp₀0
  have hC₁ := sourceIntegrand_continuousOn (x := x) hp₁0
  have hC := sourceIntegrand_continuousOn (x := x) hM0
  have hpoint (t : ℝ) (ht : 0 < t) :
      a * sourceIntegrand p₀ t + b * sourceIntegrand p₁ t <
        sourceIntegrand (a * p₀ + b * p₁) t := by
    simpa only [smul_eq_mul] using
      (sourceIntegrand_strictConcaveOn ht).2 hp₀ hp₁ hne ha hb hab
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hx (hC₀.const_mul a |>.add (hC₁.const_mul b)) hC
    (fun t ht ↦ (hpoint t ht.1).le) ⟨x, ⟨hx.le, le_rfl⟩, hpoint x hx⟩
  simp only [Pi.add_apply] at hi
  rw [intervalIntegral.integral_add
    (hC₀.intervalIntegrable_of_Icc hx.le |>.const_mul a)
    (hC₁.intervalIntegrable_of_Icc hx.le |>.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  simpa only [smul_eq_mul, sourceArcsinh] using hi

theorem source_conjecture : SourceConjecture := by
  intro x hx _
  have hs : Ioi (1 : ℝ) ⊆ Ioi (Real.log 2 / 2) := by
    intro p hp
    have hlog : Real.log 2 < 2 := lt_of_le_of_lt (Real.log_le_sub_one_of_pos (by norm_num))
      (by norm_num)
    change Real.log 2 / 2 < p
    change 1 < p at hp
    linarith
  refine ⟨convex_Ioi _, ?_⟩
  intro p₀ hp₀ p₁ hp₁ hne a b ha hb hab
  exact (sourceArcsinh_strictConcaveOn hx).2 (hs hp₀) (hs hp₁) hne ha hb hab

end ArcsinhPositive
