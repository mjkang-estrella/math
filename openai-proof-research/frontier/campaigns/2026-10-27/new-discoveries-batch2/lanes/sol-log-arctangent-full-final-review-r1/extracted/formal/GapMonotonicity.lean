import Centered
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option autoImplicit false
set_option warningAsError true
namespace LogArctangentSource
open Filter Topology
noncomputable def logExpression (t : ℝ) : ℝ :=
  (1/d)*(Real.log beta + Real.log (Real.sinh (alpha*t)) -
    (Real.log alpha + Real.log (Real.sinh (beta*t)))) -
  (Real.log (Real.sqrt 2) + Real.log (Real.sinh t) - Real.log (Real.arctan (Real.sqrt 2*t)))

theorem centeredLogGap_eq {t : ℝ} (ht : 0 < t) : centeredLogGap t = logExpression t := by
  have ha := parameters.1.trans parameters.2.1
  have hs := Real.sinh_pos_iff.mpr ht
  have hsa := Real.sinh_pos_iff.mpr (mul_pos ha ht)
  have hsb := Real.sinh_pos_iff.mpr (mul_pos parameters.1 ht)
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hat := Real.arctan_pos.mpr (mul_pos h2 ht)
  rw [centeredLogGap, centered_log_fixedS ht, centered_mean ht,
    Real.log_div (mul_pos parameters.1 hsa).ne' (mul_pos ha hsb).ne',
    Real.log_mul parameters.1.ne' hsa.ne', Real.log_mul ha.ne' hsb.ne',
    Real.log_div (mul_pos h2 hs).ne' hat.ne', Real.log_mul h2.ne' hs.ne']
  rfl

theorem hasDerivAt_centeredLogGap {t : ℝ} (ht : 0 < t) :
    HasDerivAt centeredLogGap
      (Real.sqrt 2/((1+2*t^2)*Real.arctan (Real.sqrt 2*t)) -
        LogArctangentMean.A t/LogArctangentMean.B t) t := by
  have ha := parameters.1.trans parameters.2.1
  have hs := (Real.sinh_pos_iff.mpr ht).ne'
  have hsa := (Real.sinh_pos_iff.mpr (mul_pos ha ht)).ne'
  have hsb := (Real.sinh_pos_iff.mpr (mul_pos parameters.1 ht)).ne'
  have hat : Real.arctan (Real.sqrt 2*t) ≠ 0 :=
    (Real.arctan_pos.mpr (mul_pos (Real.sqrt_pos.mpr (by norm_num)) ht)).ne'
  have h1 := ((((hasDerivAt_id t).const_mul alpha).sinh.log hsa).const_add
    (Real.log beta)).sub ((((hasDerivAt_id t).const_mul beta).sinh.log hsb).const_add
    (Real.log alpha))
  have h2 := ((Real.hasDerivAt_sinh t).log hs).const_add (Real.log (Real.sqrt 2))
  have h3 := (LogArctangentMean.hasDerivAt_centered_arctan t).log hat
  have h := (h1.const_mul (1/d)).sub (h2.sub h3)
  have he : logExpression =ᶠ[𝓝 t] centeredLogGap := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    exact (centeredLogGap_eq hx).symm
  have hh : HasDerivAt logExpression
      ((1/d)*((Real.cosh (alpha*t)*alpha)/Real.sinh (alpha*t) -
          (Real.cosh (beta*t)*beta)/Real.sinh (beta*t)) -
        (Real.cosh t/Real.sinh t -
          (Real.sqrt 2/(1+2*t^2))/Real.arctan (Real.sqrt 2*t))) t := by
    convert h using 1
    · rfl
    · simp
  convert hh.congr_of_eventuallyEq he.symm using 1
  rw [LogArctangentMean.A_over_B ht, LogArctangentMean.d_source, div_mul_eq_div_div]
  ring

theorem gap_deriv_pos_of_E_pos (hE : ∀ t : ℝ, 0<t → 0<LogArctangentMean.E t)
    {t : ℝ} (ht : 0 < t) : 0 < deriv centeredLogGap t := by
  rw [(hasDerivAt_centeredLogGap ht).deriv]
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hp : 0 < 1+2*t^2 := by positivity
  have hA := LogArctangentMean.A_pos ht
  have hB := LogArctangentMean.B_pos ht
  have hat := Real.arctan_pos.mpr (mul_pos h2 ht)
  have hJ := LogArctangentMean.J_gt_arctan hE ht
  unfold LogArctangentMean.J at hJ
  have hj := (lt_div_iff₀ (mul_pos hp hA)).mp hJ
  apply sub_pos.mpr
  apply (div_lt_div_iff₀ hB (mul_pos hp hat)).mpr
  nlinarith [hj]

theorem gap_strictMono_of_E_pos (hE : ∀ t : ℝ, 0<t → 0<LogArctangentMean.E t) :
    StrictMonoOn centeredLogGap (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro t ht; exact (hasDerivAt_centeredLogGap ht).continuousAt.continuousWithinAt
  · intro t ht
    exact gap_deriv_pos_of_E_pos hE (by simpa only [interior_Ioi, Set.mem_Ioi] using ht)

theorem sourceClaim_of_E_pos (hE : ∀ t : ℝ, 0<t → 0<LogArctangentMean.E t) :
    SourceClaim := sourceClaim_of_strictMono_gap (gap_strictMono_of_E_pos hE)
end LogArctangentSource
