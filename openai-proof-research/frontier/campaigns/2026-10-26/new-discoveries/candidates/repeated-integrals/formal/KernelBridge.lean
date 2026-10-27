import StieltjesData

open MeasureTheory Set Filter
open scoped Topology

namespace RepeatedIntegrals

noncomputable section

def cutKernel (k : ℕ) (x : ℝ) : ℝ := (1 - max 0 (min 1 x)) ^ k

theorem cutKernel_continuous (k : ℕ) : Continuous (cutKernel k) := by
  unfold cutKernel
  fun_prop

theorem cutKernel_norm_le (k : ℕ) (x : ℝ) : ‖cutKernel k x‖ ≤ 1 := by
  obtain ⟨hx0, hx1⟩ := intervalExtension_mem x
  rw [cutKernel, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith) _)]
  exact pow_le_one₀ (by linarith) (by linarith)

theorem cutKernel_of_mem (k : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    cutKernel k x = (1 - x) ^ k := by
  simp [cutKernel, min_eq_right hx.2, max_eq_right hx.1]

theorem cutKernel_tail_integral (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..1, if t ≤ x then cutKernel k x else 0) =
      (1 - t) ^ (k + 1) / (k + 1) := by
  have hset : Icc (0 : ℝ) 1 ∩ Ici t = Icc t 1 := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_Ici]
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · exact fun h => ⟨⟨ht.1.trans h.1, h.2⟩, h.1⟩
  calc
    (∫ x in (0 : ℝ)..1, if t ≤ x then cutKernel k x else 0) =
        ∫ x in Icc (0 : ℝ) 1, (Ici t).indicator (cutKernel k) x := by
      rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
      rfl
    _ = ∫ x in Icc t 1, cutKernel k x := by
      rw [setIntegral_indicator measurableSet_Ici, hset]
    _ = ∫ x in t..1, cutKernel k x := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.2]
    _ = ∫ x in t..1, (1 - x) ^ k := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le ht.2] at hx
      exact cutKernel_of_mem k ⟨ht.1.trans hx.1, hx.2⟩
    _ = ∫ x in (0 : ℝ)..(1 - t), x ^ k := by
      simpa only [sub_self] using
        (intervalIntegral.integral_comp_sub_left (a := t) (b := (1 : ℝ))
          (fun x : ℝ => x ^ k) (1 : ℝ))
    _ = (1 - t) ^ (k + 1) / (k + 1) := by
      rw [integral_pow]
      simp

theorem cdf_kernel_integral {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hs : μ (Icc (0 : ℝ) 1)ᶜ = 0) (k : ℕ) :
    (∫ x in (0 : ℝ)..1, (1 - x) ^ k * μ.real (Iic x)) =
      (∫ t, (1 - t) ^ (k + 1) ∂μ) / (k + 1) := by
  classical
  let F : ℝ → ℝ → ℝ := fun x t => if t ≤ x then cutKernel k x else 0
  let ν : Measure ℝ := volume.restrict (uIoc (0 : ℝ) 1)
  have : IsFiniteMeasure ν := by
    constructor
    simp [ν]
  have hFm : StronglyMeasurable (Function.uncurry F) := by
    exact ((cutKernel_continuous k).comp continuous_fst).stronglyMeasurable.indicator
      (isClosed_le continuous_snd continuous_fst).measurableSet
  have hFi : Integrable (Function.uncurry F) (ν.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
    apply Eventually.of_forall
    intro z
    dsimp [Function.uncurry, F]
    split_ifs
    · exact cutKernel_norm_le k z.1
    · norm_num
  have hswap := intervalIntegral_integral_swap hFi
  have hleft : (∫ x in (0 : ℝ)..1, ∫ t, F x t ∂μ) =
      ∫ x in (0 : ℝ)..1, (1 - x) ^ k * μ.real (Iic x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hi := integral_indicator_const (μ := μ) (cutKernel k x)
      (s := Iic x) measurableSet_Iic
    simpa [F, indicator, smul_eq_mul, cutKernel_of_mem k hx, mul_comm] using hi
  have ha : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hs
  have hright : (∫ t, (∫ x in (0 : ℝ)..1, F x t) ∂μ) =
      (∫ t, (1 - t) ^ (k + 1) ∂μ) / (k + 1) := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [ha] with t ht
    exact cutKernel_tail_integral k ht
  exact hleft.symm.trans (hswap.trans hright)

theorem intervalStieltjes_cdf_real {g : ℝ → ℝ}
    (hm : MonotoneOn g (Icc (0 : ℝ) 1)) (hc : ContinuousOn g (Icc (0 : ℝ) 1))
    (h0 : g 0 = 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (intervalStieltjes g hm hc).measure.real (Iic x) = g x := by
  rw [Measure.real, StieltjesFunction.measure_Iic _ (intervalStieltjes_tendsto_atBot hm hc)]
  change (ENNReal.ofReal (intervalExtension g x - g 0)).toReal = _
  rw [intervalExtension_of_mem g hx, h0, sub_zero, ENNReal.toReal_ofReal]
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) hx hx.1
  linarith

theorem intervalStieltjes_kernel {g : ℝ → ℝ}
    (hm : MonotoneOn g (Icc (0 : ℝ) 1)) (hc : ContinuousOn g (Icc (0 : ℝ) 1))
    (h0 : g 0 = 0) (k : ℕ) :
    (∫ x in (0 : ℝ)..1, (1 - x) ^ k * g x) =
      (∫ t, (1 - t) ^ (k + 1) ∂(intervalStieltjes g hm hc).measure) / (k + 1) := by
  let := intervalStieltjes_finite hm hc
  rw [← cdf_kernel_integral (intervalStieltjes_compl hm hc) k]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  change (1 - x) ^ k * g x =
    (1 - x) ^ k * (intervalStieltjes g hm hc).measure.real (Iic x)
  rw [intervalStieltjes_cdf_real hm hc h0 hx]

end

end RepeatedIntegrals
