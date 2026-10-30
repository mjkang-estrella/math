module
public import EndpointTwo
public section
noncomputable section
open Real MeasureTheory Set Filter
open scoped Topology
namespace PendulumTimeMap
theorem b_mem {z : ℝ} (hz : z∈Icc 0 2) : b z∈Icc 0 (Real.pi/2) := by
 constructor
 · unfold b; exact div_nonneg (Real.arccos_nonneg _) (by norm_num)
 · unfold b
   have := Real.arccos_le_pi (1-z)
   linarith
theorem moving_denominator {phi z x : ℝ} (hz : z∈Icc 0 2) (hx : x∈Icc 0 (b z)) :
 a phi ≤ z-Real.cos (2*phi)+Real.cos (2*x) := by
 have hb := b_mem hz
 have hh := Real.cos_le_cos_of_nonneg_of_le_pi (x := 2*x) (y := 2*b z)
   (by linarith [hx.1]) (by linarith [hb.2]) (by linarith [hx.2])
 have he := a_b hz.1 hz.2
 unfold a at *
 linarith
theorem moving_source_integrable {phi z : ℝ} (hp : 0<phi) (hp1 : phi<Real.pi/2)
 (hz : z∈Icc 0 2) : IntervalIntegrable (sourceKernel phi z) volume 0 (b z) := by
 have ha := (a_range hp hp1).1
 apply ContinuousOn.intervalIntegrable_of_Icc (a := 0) (b_mem hz).1
 apply ContinuousOn.inv₀
 · exact (continuous_const.add ((continuous_id.const_mul 2).cos)).sqrt.continuousOn
 · intro x hx
   exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le ha (moving_denominator hz hx)))
theorem moving_source_continuousOn {phi : ℝ} (hp : 0<phi) (hp1 : phi<Real.pi/2) :
 ContinuousOn (fun z => ∫ x in 0..b z, sourceKernel phi z x) (Icc 0 2) := by
 let g : ℝ → ℝ → ℝ := fun z x =>
   (Real.sqrt (max (a phi/2) (z-Real.cos (2*phi)+Real.cos (2*x))))⁻¹
 have ha := (a_range hp hp1).1
 have hg : Continuous g.uncurry := by
   apply Continuous.inv₀
   · fun_prop
   · intro p
     exact ne_of_gt (Real.sqrt_pos.mpr
       (lt_of_lt_of_le (by positivity : 0<a phi/2) (le_max_left _ _)))
 have hc := intervalIntegral.continuous_parametric_primitive_of_continuous
   (μ := volume) (a₀ := 0) hg
 have hmoving : Continuous (fun z => ∫ x in 0..b z, g z x) :=
   hc.comp (continuous_id.prodMk b_continuous)
 apply hmoving.continuousOn.congr
 intro z hz
 apply intervalIntegral.integral_congr
 rw [uIcc_of_le (b_mem hz).1]
 intro x hx
 dsimp [g,sourceKernel]
 rw [max_eq_right (by linarith [moving_denominator (phi := phi) hz hx])]
end PendulumTimeMap
