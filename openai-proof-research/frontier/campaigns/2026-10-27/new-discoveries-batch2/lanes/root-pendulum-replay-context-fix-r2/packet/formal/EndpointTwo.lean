module
public import Source
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public section
noncomputable section
open Real MeasureTheory Set Filter
open scoped Topology
namespace PendulumTimeMap
theorem b_continuous : Continuous b := by unfold b; fun_prop
theorem b_zero : b 0=0 := by simp [b]
theorem b_two : b 2=Real.pi/2 := by norm_num [b]
theorem source_denominator_near_two {phi z x : ℝ}
 (hz : 2-a phi/2 ≤ z) :
 a phi/2 ≤ z-Real.cos (2*phi)+Real.cos (2*x) := by
 have h := Real.neg_one_le_cos (2*x)
 unfold a at *
 linarith
theorem sourceKernel_continuous_near_two {phi : ℝ}
 (hp : 0<phi) (hp1 : phi<Real.pi/2) :
 ∃ g : ℝ → ℝ → ℝ, Continuous g.uncurry ∧
 ∀ z, 2-a phi/2 ≤ z → ∀ x, g z x=sourceKernel phi z x := by
 let g : ℝ → ℝ → ℝ := fun z x =>
   (Real.sqrt (max (a phi/2) (z-Real.cos (2*phi)+Real.cos (2*x))))⁻¹
 have ha := (a_range hp hp1).1
 refine ⟨g, ?_, ?_⟩
 · apply Continuous.inv₀
   · fun_prop
   · intro p
     apply ne_of_gt
     apply Real.sqrt_pos.mpr
     exact lt_of_lt_of_le (by positivity : 0<a phi/2) (le_max_left _ _)
 · intro z hz x
   dsimp [g,sourceKernel]
   rw [max_eq_right (source_denominator_near_two hz)]
theorem source_integrable_two {phi : ℝ} (hp : 0<phi) (hp1 : phi<Real.pi/2) :
 IntervalIntegrable (sourceKernel phi 2) volume 0 phi ∧
 IntervalIntegrable (sourceKernel phi 2) volume 0 (b 2) := by
 obtain ⟨g,hg,he⟩ := sourceKernel_continuous_near_two hp hp1
 have ha := (a_range hp hp1).1
 have hge : g 2=sourceKernel phi 2 := funext (he 2 (by linarith))
 have hc : Continuous (sourceKernel phi 2) := by
   rw [← hge]
   exact hg.comp (continuous_const.prodMk continuous_id)
 exact ⟨hc.intervalIntegrable _ _,hc.intervalIntegrable _ _⟩
theorem sourceTime_continuousAt_two {phi : ℝ} (hp : 0<phi) (hp1 : phi<Real.pi/2) :
 ContinuousAt (sourceTime phi) 2 := by
 obtain ⟨g,hg,he⟩ := sourceKernel_continuous_near_two hp hp1
 have hc := intervalIntegral.continuous_parametric_primitive_of_continuous
   (μ := volume) (a₀ := 0) hg
 have hfixed : Continuous (fun z => ∫ x in 0..phi, g z x) :=
   hc.comp (continuous_id.prodMk continuous_const)
 have hmoving : Continuous (fun z => ∫ x in 0..b z, g z x) :=
   hc.comp (continuous_id.prodMk b_continuous)
 have ha := (a_range hp hp1).1
 have ht : 2-a phi/2 < (2:ℝ) := by linarith
 have heq : sourceTime phi =ᶠ[𝓝 2]
   (fun z => (∫ x in 0..phi, g z x)+(∫ x in 0..b z, g z x)) := by
   filter_upwards [Ioi_mem_nhds ht] with z hz
   have hh : g z=sourceKernel phi z := funext (he z hz.le)
   simp only [sourceTime,hh]
 exact (hfixed.add hmoving).continuousAt.congr_of_eventuallyEq heq
end PendulumTimeMap
