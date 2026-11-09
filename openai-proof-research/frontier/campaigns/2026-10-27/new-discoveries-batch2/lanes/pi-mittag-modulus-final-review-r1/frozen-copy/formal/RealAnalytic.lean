import SourceDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ContDiff

namespace MittagModulus

noncomputable def mittagReal (a b t : ℝ) : ℝ :=
  ∑' n : ℕ, t ^ n / Real.Gamma (a * (n : ℝ) + b)

noncomputable def mittagScalarSeries (a b : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => 1 / Real.Gamma (a * (n : ℝ) + b))

theorem mittagScalarSeries_radius {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (mittagScalarSeries a b).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have h := mittag_real_majorant_summable ha hb r.coe_nonneg
  convert h using 1
  ext n
  simp only [mittagScalarSeries, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / Real.Gamma (a * (n : ℝ) + b))]
  ring

theorem mittagScalarSeries_sum (a b : ℝ) :
    (mittagScalarSeries a b).sum = mittagReal a b := by
  funext t
  change FormalMultilinearSeries.ofScalarsSum
    (fun n : ℕ => 1 / Real.Gamma (a * (n : ℝ) + b)) t = mittagReal a b t
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  unfold mittagReal
  apply tsum_congr
  intro n
  simp only [smul_eq_mul]
  ring

theorem mittagReal_analyticAt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    AnalyticAt ℝ (mittagReal a b) t := by
  have hr := mittagScalarSeries_radius ha hb
  have hp := (mittagScalarSeries a b).hasFPowerSeriesOnBall (by rw [hr]; exact ENNReal.zero_lt_top)
  rw [mittagScalarSeries_sum] at hp
  exact hp.analyticAt_of_mem (by simp [hr])

theorem mittagReal_contDiff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContDiff ℝ ∞ (mittagReal a b) := by
  rw [contDiff_iff_contDiffAt]
  exact fun t => (mittagReal_analyticAt ha hb t).contDiffAt

theorem mittagLeffler_ofReal (a b t : ℝ) :
    mittagLeffler a b (t : ℂ) = (mittagReal a b t : ℂ) := by
  unfold mittagLeffler mittagReal
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  push_cast
  rfl

theorem sourceExpression_real (a t : ℝ) :
    sourceExpression a t = mittagReal (2 * a) 1 (-t) ^ 2 +
      t * mittagReal (2 * a) (1 + a) (-t) ^ 2 := by
  unfold sourceExpression
  rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by simp, mittagLeffler_ofReal,
    mittagLeffler_ofReal, Complex.normSq_ofReal, Complex.normSq_ofReal]
  ring

theorem sourceExpression_contDiff {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ ∞ (sourceExpression a) := by
  have he : sourceExpression a = fun t : ℝ => mittagReal (2 * a) 1 (-t) ^ 2 +
      t * mittagReal (2 * a) (1 + a) (-t) ^ 2 := funext (sourceExpression_real a)
  rw [he]
  apply ContDiff.add
  · exact ((mittagReal_contDiff (by positivity : 0 < 2 * a) zero_lt_one).comp
      contDiff_id.neg).pow 2
  · exact contDiff_id.mul (((mittagReal_contDiff (by positivity : 0 < 2 * a)
      (by positivity : 0 < 1 + a)).comp contDiff_id.neg).pow 2)

end MittagModulus
