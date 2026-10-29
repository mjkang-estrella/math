module
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public section
set_option autoImplicit false
set_option warningAsError true
open Real MeasureTheory Set Filter Asymptotics
namespace Renyi
theorem moment_integrable {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun u : ℝ => exp (-p*u)*u^p) (Ioi 0) := by
  have hc : Continuous (fun u : ℝ => u^p) := continuous_id.rpow_const (by
    intro u; exact Or.inr hp.le)
  have H := integrableOn_exp_neg_mul_of_isBigO_exp (c := (0:ℝ))
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ici)
    (isLittleO_rpow_exp_pos_mul_atTop p (show 0 < p/2 by linarith)).isBigO
    (show p/2 < p by linarith)
  exact H.mono_set Ioi_subset_Ici_self

theorem majorant_integrable {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun u : ℝ => exp (-p*u) * (2*u)^p) (Ioi 0) := by
  apply ((moment_integrable hp).const_mul ((2:ℝ)^p)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [mul_rpow (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hu)]
  ring

end Renyi
