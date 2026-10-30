module
public import EndpointZero
public import MovingEndpoint
public section
noncomputable section
open Real MeasureTheory Set Filter
open scoped Topology
namespace PendulumTimeMap
theorem sourceKernel_measurable (phi z : ℝ) : Measurable (sourceKernel phi z) := by
 unfold sourceKernel
 fun_prop
theorem source_denominator_zero_pos {phi x : ℝ} (_hp : 0<phi) (hp1 : phi<Real.pi/2)
 (hx : x∈Ico 0 phi) : 0<0-Real.cos (2*phi)+Real.cos (2*x) := by
 have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 2*x) (y := 2*phi)
   (by linarith [hx.1]) (by linarith) (by linarith [hx.2])
 linarith
theorem sourceKernel_le_zero {phi z x : ℝ} (hz : 0≤z)
 (hx : 0<0-Real.cos (2*phi)+Real.cos (2*x)) :
 ‖sourceKernel phi z x‖ ≤ sourceKernel phi 0 x := by
 have hsq := Real.sqrt_pos.mpr hx
 unfold sourceKernel
 rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
 exact inv_anti₀ hsq (Real.sqrt_le_sqrt (by linarith))
theorem fixed_source_continuousWithinAt_zero {phi : ℝ}
 (hp : 0<phi) (hp1 : phi<Real.pi/2) :
 ContinuousWithinAt (fun z => ∫ x in 0..phi, sourceKernel phi z x) (Icc 0 2) 0 := by
 have h_ae : ∀ᵐ x : ℝ ∂volume, x≠phi := by
   exact ae_iff.mpr (by simp)
 apply intervalIntegral.continuousWithinAt_of_dominated_interval
   (bound := sourceKernel phi 0)
 · exact Eventually.of_forall (fun z => (sourceKernel_measurable phi z).aestronglyMeasurable)
 · filter_upwards [self_mem_nhdsWithin] with z hz
   filter_upwards [h_ae] with x hx hmem
   rw [uIoc_of_le hp.le] at hmem
   exact sourceKernel_le_zero hz.1 (source_denominator_zero_pos hp hp1
     ⟨hmem.1.le,lt_of_le_of_ne hmem.2 hx⟩)
 · exact source_integrable_zero hp hp1
 · filter_upwards [h_ae] with x hx hmem
   rw [uIoc_of_le hp.le] at hmem
   have hpos := source_denominator_zero_pos hp hp1 ⟨hmem.1.le,lt_of_le_of_ne hmem.2 hx⟩
   apply ContinuousAt.continuousWithinAt
   apply ContinuousAt.inv₀
   · fun_prop
   · exact ne_of_gt (Real.sqrt_pos.mpr hpos)
theorem sourceTime_continuousWithinAt_zero {phi : ℝ}
 (hp : 0<phi) (hp1 : phi<Real.pi/2) :
 ContinuousWithinAt (sourceTime phi) (Icc 0 2) 0 := by
 exact (fixed_source_continuousWithinAt_zero hp hp1).add
   (moving_source_continuousOn hp hp1 0 ⟨le_rfl,by norm_num⟩)
end PendulumTimeMap
