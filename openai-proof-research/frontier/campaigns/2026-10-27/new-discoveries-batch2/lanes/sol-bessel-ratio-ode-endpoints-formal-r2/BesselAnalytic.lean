module
public import BesselRatio
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public section
noncomputable section
open scoped Topology
open Filter
namespace BesselRatio

theorem S_eq_powerSeries (ν : ℝ) :
    S ν = (FormalMultilinearSeries.ofScalars ℝ (coeff ν)).sum := by
  funext t
  simpa only [S, smul_eq_mul, FormalMultilinearSeries.ofScalarsSum] using
    (FormalMultilinearSeries.ofScalars_sum_eq (coeff ν) t).symm

theorem series_radius {ν : ℝ} (hν : -1 < ν) :
    (FormalMultilinearSeries.ofScalars ℝ (coeff ν)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  simpa only [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs,
    abs_of_pos (coeff_pos hν _)] using (summable_S (t := (r:ℝ)) hν)

theorem S_analytic {ν : ℝ} (hν : -1 < ν) (t : ℝ) : AnalyticAt ℝ (S ν) t := by
  rw [S_eq_powerSeries]
  apply FormalMultilinearSeries.analyticOnNhd
  simp [series_radius hν]

theorem S_zero (ν : ℝ) : S ν 0 = 1 / Real.Gamma (ν+1) := by
  rw [S_eq_powerSeries]
  simpa [FormalMultilinearSeries.ofScalarsSum, coeff] using
    (FormalMultilinearSeries.ofScalarsSum_zero (E := ℝ) (coeff ν))

theorem S_hasDerivAt {ν : ℝ} (hν : -1 < ν) (t : ℝ) :
    HasDerivAt (S ν) (deriv (S ν) t) t :=
  (S_analytic hν t).differentiableAt.hasDerivAt

/-- Global convergent power-series representation, with no local convergence premise. -/
theorem S_hasFPowerSeries {ν : ℝ} (hν : -1 < ν) :
    HasFPowerSeriesOnBall (S ν) (FormalMultilinearSeries.ofScalars ℝ (coeff ν)) 0 ⊤ := by
  rw [S_eq_powerSeries, ← series_radius hν]
  exact FormalMultilinearSeries.hasFPowerSeriesOnBall _ (by rw [series_radius hν]; simp)

theorem F_zero {ν : ℝ} (hν : -1 < ν) : F ν 0 = 1 := by
  unfold F
  rw [S_zero]
  exact mul_one_div_cancel (Real.Gamma_pos_of_pos (by linarith : 0 < ν+1)).ne'

/-- Normalized Euler factor; this is an explicit function of the literal series. -/
@[expose] def euler (ν t : ℝ) : ℝ := ν * S ν t + 2 * t * deriv (S ν) t

theorem euler_continuousAt {ν : ℝ} (hν : -1 < ν) (t : ℝ) :
    ContinuousAt (euler ν) t := by
  unfold euler
  exact ((S_analytic hν t).continuousAt.const_mul ν).add
    ((continuousAt_id.const_mul 2).mul (S_analytic hν t).deriv.continuousAt)

theorem euler_zero (ν : ℝ) : euler ν 0 = ν / Real.Gamma (ν+1) := by
  simp [euler, S_zero, div_eq_mul_inv]

/-- The normalized Wronskian coefficient. Its identification with the literal
Wronskian is a remaining derivative/algebra obligation, not a hypothesis here. -/
@[expose] def wCoefficient (u v a b x : ℝ) : ℝ :=
  euler u ((a*x)^2) * S v ((b*x)^2) -
    S u ((a*x)^2) * euler v ((b*x)^2)

theorem wCoefficient_limit {u v : ℝ} (hu : -1 < u) (hv : -1 < v) (a b : ℝ) :
    Tendsto (wCoefficient u v a b) (𝓝 0)
      (𝓝 ((u-v) / (Real.Gamma (u+1) * Real.Gamma (v+1)))) := by
  have ha : ContinuousAt (fun x : ℝ => (a*x)^2) 0 :=
    (continuousAt_id.const_mul a).pow 2
  have hb : ContinuousAt (fun x : ℝ => (b*x)^2) 0 :=
    (continuousAt_id.const_mul b).pow 2
  have heua : ContinuousAt (fun x : ℝ => euler u ((a*x)^2)) 0 :=
    by
    have he : ContinuousAt (euler u) ((a*0)^2) := by simpa using euler_continuousAt hu 0
    exact he.comp (f := fun x : ℝ => (a*x)^2) ha
  have heub : ContinuousAt (fun x : ℝ => euler v ((b*x)^2)) 0 :=
    by
    have he : ContinuousAt (euler v) ((b*0)^2) := by simpa using euler_continuousAt hv 0
    exact he.comp (f := fun x : ℝ => (b*x)^2) hb
  have hsa : ContinuousAt (fun x : ℝ => S u ((a*x)^2)) 0 :=
    by
    have he : ContinuousAt (S u) ((a*0)^2) := by simpa using (S_analytic hu 0).continuousAt
    exact he.comp (f := fun x : ℝ => (a*x)^2) ha
  have hsb : ContinuousAt (fun x : ℝ => S v ((b*x)^2)) 0 :=
    by
    have he : ContinuousAt (S v) ((b*0)^2) := by simpa using (S_analytic hv 0).continuousAt
    exact he.comp (f := fun x : ℝ => (b*x)^2) hb
  convert ((heua.mul hsb).sub (hsa.mul heub)).tendsto using 1
  · rfl
  · congr 1
    dsimp
    simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), euler_zero, S_zero]
    ring

/-- Closed first derivative of the literal source series at every positive argument. -/
theorem I_hasDerivAt {ν z : ℝ} (hν : -1 < ν) (hz : 0 < z) :
    HasDerivAt (I ν)
      ((ν * (z/2)^(ν-1) * (1/2)) * S ν (z^2) +
        (z/2)^ν * (deriv (S ν) (z^2) * (2*z))) z := by
  have hp := ((hasDerivAt_id z).div_const 2).rpow_const
    (Or.inl (by positivity : z/2 ≠ 0)) (p := ν)
  have hs := (S_hasDerivAt hν (z^2)).comp z ((hasDerivAt_id z).pow 2)
  have hd := hp.mul hs
  have heq : I ν =ᶠ[𝓝 z] (fun y : ℝ => (y/2)^ν * S ν (y^2)) := by
    filter_upwards [eventually_gt_nhds hz] with y hy
    exact I_eq_rpow_mul_S hy
  convert hd.congr_of_eventuallyEq heq using 1
  dsimp
  ring

end BesselRatio
