import MomentDefs

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology BigOperators

namespace RepeatedIntegrals

noncomputable section

def endpointBump (c δ : ℝ) (hδ : 0 < δ) : ContDiffBump c :=
  ⟨δ / 2, δ, by linarith, by linarith⟩

theorem endpointBump_eventually_zero (c δ : ℝ) (hδ : 0 < δ) (x : ℝ)
    (hx : δ < dist x c) : endpointBump c δ hδ =ᶠ[𝓝 x] fun _ => 0 := by
  have he : ∀ᶠ y in 𝓝 x, δ < dist y c :=
    ((continuous_id.dist continuous_const).continuousAt).eventually (lt_mem_nhds hx)
  filter_upwards [he] with y hy
  exact (endpointBump c δ hδ).zero_of_le_dist hy.le

def endpointBaseline (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : ℝ :=
  δ + (1 - δ) * (endpointBump 0 δ hδ x + endpointBump 1 δ hδ x)

theorem endpointBaseline_smooth (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (endpointBaseline δ hδ) := by
  exact contDiff_const.add (contDiff_const.mul
    ((endpointBump 0 δ hδ).contDiff.add (endpointBump 1 δ hδ).contDiff))

theorem endpointBaseline_pos (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (x : ℝ) :
    0 < endpointBaseline δ hδ x := by
  have h0 := (endpointBump 0 δ hδ).nonneg' x
  have h1 := (endpointBump 1 δ hδ).nonneg' x
  dsimp [endpointBaseline]
  positivity

theorem endpointBaseline_good (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    GoodDensity (endpointBaseline δ hδ) := by
  refine ⟨endpointBaseline_smooth δ hδ,
    fun x _ => endpointBaseline_pos δ hδ hδ1 x, ?_, ?_⟩
  · have hz := endpointBump_eventually_zero 1 δ hδ 0 (by simpa using hδ1)
    filter_upwards [(endpointBump 0 δ hδ).eventuallyEq_one, hz] with x hx0 hx1
    simp only [endpointBaseline, hx0, hx1, Pi.one_apply, add_zero, mul_one]
    ring
  · have hz := endpointBump_eventually_zero 0 δ hδ 1 (by simpa using hδ1)
    filter_upwards [hz, (endpointBump 1 δ hδ).eventuallyEq_one] with x hx0 hx1
    simp only [endpointBaseline, hx0, hx1, Pi.one_apply, zero_add, mul_one]
    ring

theorem endpointBump_interval_bound (c δ : ℝ) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..1, endpointBump c δ hδ t) ≤ 2 * δ := by
  calc
    (∫ t in (0 : ℝ)..1, endpointBump c δ hδ t) ≤
        ∫ t, endpointBump c δ hδ t := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact setIntegral_le_integral (endpointBump c δ hδ).integrable
        (Eventually.of_forall (endpointBump c δ hδ).nonneg')
    _ ≤ volume.real (closedBall c (endpointBump c δ hδ).rOut) :=
      (endpointBump c δ hδ).integral_le_measure_closedBall volume
    _ = 2 * δ := by
      exact Real.volume_real_closedBall hδ.le

theorem endpointBaseline_mass_bound (δ : ℝ) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..1, endpointBaseline δ hδ t) ≤ 5 * δ := by
  have h0 := endpointBump_interval_bound 0 δ hδ
  have h1 := endpointBump_interval_bound 1 δ hδ
  have hn0 : 0 ≤ ∫ t in (0 : ℝ)..1, endpointBump 0 δ hδ t :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (endpointBump 0 δ hδ).nonneg'
  have hn1 : 0 ≤ ∫ t in (0 : ℝ)..1, endpointBump 1 δ hδ t :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (endpointBump 1 δ hδ).nonneg'
  have hc0 := (endpointBump 0 δ hδ).continuous.intervalIntegrable (μ := volume) 0 1
  have hc1 := (endpointBump 1 δ hδ).continuous.intervalIntegrable (μ := volume) 0 1
  unfold endpointBaseline
  rw [intervalIntegral.integral_add (intervalIntegrable_const)
    ((hc0.add hc1).const_mul (1 - δ)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hc0 hc1]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  nlinarith

theorem endpointBaseline_moment_bounds (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (i : Fin (n + 1)) :
    0 ≤ densityMoments n (endpointBaseline δ hδ) i ∧
      densityMoments n (endpointBaseline δ hδ) i ≤ 5 * δ := by
  have hc := (endpointBaseline_smooth δ hδ).continuous
  have hp := endpointBaseline_pos δ hδ hδ1
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    exact mul_nonneg (pow_nonneg ht.1 _) (hp t).le
  · apply le_trans _ (endpointBaseline_mass_bound δ hδ)
    apply intervalIntegral.integral_mono_on (by norm_num)
      (((continuous_id.pow _).mul hc).intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
    intro t ht
    exact mul_le_of_le_one_left (hp t).le (pow_le_one₀ ht.1 ht.2)

theorem zero_mem_closure_smoothMomentSet (n : ℕ) :
    (0 : MomentSpace n) ∈ closure (smoothMomentSet n) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ := min (ε / 10) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨densityMoments n (endpointBaseline δ hδ),
    ⟨endpointBaseline δ hδ, endpointBaseline_good δ hδ hδ1, rfl⟩, ?_⟩
  rw [dist_zero_left]
  apply lt_of_le_of_lt (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 5 * δ) |>.mpr ?_)
  · have h := min_le_left (ε / 10) (1 / 2 : ℝ)
    change δ ≤ ε / 10 at h
    linarith
  · intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (endpointBaseline_moment_bounds n δ hδ hδ1 i).1]
    exact (endpointBaseline_moment_bounds n δ hδ hδ1 i).2

end

end RepeatedIntegrals
