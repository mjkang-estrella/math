import SourceEndpoint

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace GauntIntegral

theorem negative_near_zero_of_second_derivative {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hc : ContinuousAt f'' 0) (h0 : f 0 = 0) (h0' : f' 0 = 0) (h0'' : f'' 0 < 0) :
    ∃ e : ℝ, 0 < e ∧ ∀ u ∈ Ioc 0 e, f u < 0 := by
  have hevent : {u : ℝ | f'' u < 0} ∈ 𝓝 0 := hc.eventually (gt_mem_nhds h0'')
  obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hsmall : ∀ u ∈ Icc (0 : ℝ) (e / 2), f'' u < 0 := by
    intro u hu
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
    linarith [hu.2]
  have hanti' : StrictAntiOn f' (Icc (0 : ℝ) (e / 2)) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 (e / 2))
      (fun u _ => (hf' u).continuousAt.continuousWithinAt)
      (fun u _ => (hf' u).hasDerivWithinAt)
    intro u hu
    exact hsmall u (interior_subset hu)
  have hprime : ∀ u ∈ Ioc (0 : ℝ) (e / 2), f' u < 0 := by
    intro u hu
    have h := hanti' (show (0 : ℝ) ∈ Icc (0 : ℝ) (e / 2) by constructor; rfl; linarith)
      ⟨hu.1.le, hu.2⟩ hu.1
    simpa only [h0'] using h
  have hanti : StrictAntiOn f (Icc (0 : ℝ) (e / 2)) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 (e / 2))
      (fun u _ => (hf u).continuousAt.continuousWithinAt)
      (fun u _ => (hf u).hasDerivWithinAt)
    intro u hu
    rw [interior_Icc] at hu
    exact hprime u ⟨hu.1, hu.2.le⟩
  refine ⟨e / 2, by linarith, ?_⟩
  intro u hu
  have h := hanti (show (0 : ℝ) ∈ Icc (0 : ℝ) (e / 2) by constructor; rfl; linarith)
    ⟨hu.1.le, hu.2⟩ hu.1
  simpa only [h0] using h

end GauntIntegral
