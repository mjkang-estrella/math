import KernelDerivative

set_option autoImplicit false

noncomputable section
open Set Filter Topology

namespace ArcsinhPositive

theorem expKernel_strictConcaveOn (a : ℝ) :
    StrictConcaveOn ℝ (Ioi (Real.log 2 / 2)) (expKernel a) := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi _)
  · intro p hp
    have hp0 : 0 < p := lt_trans (by positivity : 0 < Real.log 2 / 2) hp
    exact (hasDerivAt_expKernel a (ne_of_gt hp0)).continuousAt.continuousWithinAt
  · intro p hp
    have hp0 : 0 < p := lt_trans (by positivity : 0 < Real.log 2 / 2) hp
    have hd : deriv (expKernel a) =ᶠ[𝓝 p] kernelDerivative a := by
      filter_upwards [isOpen_Ioi.mem_nhds hp0] with q hq
      exact (hasDerivAt_expKernel a (ne_of_gt hq)).deriv
    have hdd := (hasDerivAt_kernelDerivative a (ne_of_gt hp0)).congr_of_eventuallyEq hd
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
    rw [hdd.deriv]
    apply mul_neg_of_pos_of_neg
    · exact div_pos (Real.exp_pos _) (pow_pos hp0 4)
    · have hb := entropyExpression_bounds (Real.exp_pos (a * p))
      have hlt : entropyExpression (Real.exp (a * p)) - 2 * p < 0 := by
        change Real.log 2 / 2 < p at hp
        linarith [hb.2]
      have hn := mul_neg_of_pos_of_neg hb.1 hlt
      have hv : 0 ≤ p ^ 3 * a ^ 2 * Real.exp (a * p) /
          (1 + Real.exp (a * p)) ^ 2 := by positivity
      nlinarith

theorem sourceIntegrand_eq_expKernel {t : ℝ} (ht : 0 < t) (p : ℝ) :
    sourceIntegrand p t = expKernel (Real.log t) p := by
  unfold sourceIntegrand expKernel
  rw [Real.rpow_def_of_pos ht,
    Real.rpow_def_of_pos (by positivity : 0 < 1 + Real.exp (Real.log t * p))]
  congr 1
  ring

theorem sourceIntegrand_strictConcaveOn {t : ℝ} (ht : 0 < t) :
    StrictConcaveOn ℝ (Ioi (Real.log 2 / 2)) (fun p ↦ sourceIntegrand p t) := by
  have heq : (fun p ↦ sourceIntegrand p t) = expKernel (Real.log t) := by
    funext p
    exact sourceIntegrand_eq_expKernel ht p
  rw [heq]
  exact expKernel_strictConcaveOn _

end ArcsinhPositive
