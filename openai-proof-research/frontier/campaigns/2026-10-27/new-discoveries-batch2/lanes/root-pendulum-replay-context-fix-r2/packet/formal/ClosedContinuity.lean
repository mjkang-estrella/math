module
public import EndpointContinuity
public section
noncomputable section
open Real MeasureTheory Set Filter
open scoped Topology
namespace PendulumTimeMap
theorem fixed_source_continuousAt_pos {phi z₀ : ℝ}
 (hp : 0<phi) (hp1 : phi<Real.pi/2) (hz₀ : 0<z₀) :
 ContinuousAt (fun z => ∫ x in 0..phi, sourceKernel phi z x) z₀ := by
 let g : ℝ → ℝ → ℝ := fun z x =>
   (Real.sqrt (max (z₀/2) (z-Real.cos (2*phi)+Real.cos (2*x))))⁻¹
 have hg : Continuous g.uncurry := by
   apply Continuous.inv₀
   · fun_prop
   · intro p
     exact ne_of_gt (Real.sqrt_pos.mpr
       (lt_of_lt_of_le (by positivity : 0<z₀/2) (le_max_left _ _)))
 have hc := intervalIntegral.continuous_parametric_primitive_of_continuous
   (μ := volume) (a₀ := 0) hg
 have hfixed : Continuous (fun z => ∫ x in 0..phi, g z x) :=
   hc.comp (continuous_id.prodMk continuous_const)
 apply hfixed.continuousAt.congr_of_eventuallyEq
 filter_upwards [Ioi_mem_nhds (show z₀/2<z₀ by linarith)] with z hz
 apply intervalIntegral.integral_congr
 rw [uIcc_of_le hp.le]
 intro x hx
 have hh := Real.cos_le_cos_of_nonneg_of_le_pi (x := 2*x) (y := 2*phi)
   (by linarith [hx.1]) (by linarith) (by linarith [hx.2])
 dsimp [g,sourceKernel]
 rw [max_eq_right (by linarith [show z₀/2<z from hz])]
theorem sourceTime_continuousOn {phi : ℝ} (hp : 0<phi) (hp1 : phi<Real.pi/2) :
 ContinuousOn (sourceTime phi) (Icc 0 2) := by
 intro z hz
 by_cases h0 : z=0
 · subst z; exact sourceTime_continuousWithinAt_zero hp hp1
 exact (fixed_source_continuousAt_pos hp hp1 (lt_of_le_of_ne hz.1 (Ne.symm h0))).continuousWithinAt.add
   (moving_source_continuousOn hp hp1 z hz)
theorem source_integrable_closed {phi z : ℝ} (hp : 0<phi) (hp1 : phi<Real.pi/2)
 (hz : z∈Icc 0 2) :
 IntervalIntegrable (sourceKernel phi z) volume 0 phi ∧
 IntervalIntegrable (sourceKernel phi z) volume 0 (b z) := by
 refine ⟨?_,moving_source_integrable hp hp1 hz⟩
 by_cases h0 : z=0
 · subst z; exact source_integrable_zero hp hp1
 by_cases h2 : z=2
 · subst z; exact (source_integrable_two hp hp1).1
 exact (source_integrable hp hp1 (lt_of_le_of_ne hz.1 (Ne.symm h0))
   (lt_of_le_of_ne hz.2 h2)).1
end PendulumTimeMap
