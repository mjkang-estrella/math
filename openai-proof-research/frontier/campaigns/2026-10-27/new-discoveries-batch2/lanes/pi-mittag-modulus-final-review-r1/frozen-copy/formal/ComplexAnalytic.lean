import AveragingRepresentation

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MittagModulus

noncomputable def mittagComplexSeries (a b : ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n : ℕ => (1 : ℂ) / (Real.Gamma (a * (n : ℝ) + b) : ℂ))

theorem mittagComplexSeries_radius {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (mittagComplexSeries a b).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have h := mittag_real_majorant_summable ha hb r.coe_nonneg
  convert h using 1
  ext n
  simp only [mittagComplexSeries, FormalMultilinearSeries.ofScalars_norm,
    norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (Real.Gamma_pos_of_pos (by positivity : 0 < a * (n : ℝ) + b))]
  ring

theorem mittagComplexSeries_sum (a b : ℝ) :
    (mittagComplexSeries a b).sum = mittagLeffler a b := by
  funext z
  change FormalMultilinearSeries.ofScalarsSum
    (fun n : ℕ => (1 : ℂ) / (Real.Gamma (a * (n : ℝ) + b) : ℂ)) z =
      mittagLeffler a b z
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  unfold mittagLeffler
  apply tsum_congr
  intro n
  simp only [smul_eq_mul]
  ring

theorem mittagLeffler_analyticAt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    AnalyticAt ℂ (mittagLeffler a b) z := by
  have hr := mittagComplexSeries_radius ha hb
  have hp := (mittagComplexSeries a b).hasFPowerSeriesOnBall
    (by rw [hr]; exact ENNReal.zero_lt_top)
  rw [mittagComplexSeries_sum] at hp
  exact hp.analyticAt_of_mem (by simp [hr])

theorem mittagLeffler_continuous {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous (mittagLeffler a b) :=
  continuous_iff_continuousAt.mpr (fun z => (mittagLeffler_analyticAt ha hb z).continuousAt)

end MittagModulus
