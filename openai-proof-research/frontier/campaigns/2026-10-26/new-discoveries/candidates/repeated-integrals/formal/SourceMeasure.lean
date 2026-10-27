import KernelBridge
import JetIntegral

open MeasureTheory Set

namespace RepeatedIntegrals

noncomputable section

structure SourceMeasure (n : ℕ) (b : MomentSpace n) where
  measure : Measure ℝ
  finite : IsFiniteMeasure measure
  atomless : NullSingletonClass measure
  supported : measure (Icc (0 : ℝ) 1)ᶜ = 0
  mass_pos : 0 < measure.real univ
  jets : ∀ j : Fin (n + 1), b j =
    (∫ t, (1 - t) ^ (n - j.val) ∂measure) / ((n - j.val).factorial : ℝ)

theorem intervalStieltjes_mass_real {g : ℝ → ℝ}
    (hm : MonotoneOn g (Icc (0 : ℝ) 1)) (hc : ContinuousOn g (Icc (0 : ℝ) 1))
    (h0 : g 0 = 0) : (intervalStieltjes g hm hc).measure.real univ = g 1 := by
  rw [Measure.real, intervalStieltjes_mass hm hc, h0, sub_zero, ENNReal.toReal_ofReal]
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num)
  linarith

theorem source_measure_exists {n : ℕ} {b : MomentSpace n} (hb : b ∈ SourceW n) :
    Nonempty (SourceMeasure n b) := by
  classical
  obtain ⟨f, hf, hm, hn, h0, ht⟩ := hb
  let g := iteratedDerivWithin n f (Icc (0 : ℝ) 1)
  have hc : ContinuousOn g (Icc (0 : ℝ) 1) := source_top_derivative_continuous hf
  have hg0 : g 0 = 0 := h0 n le_rfl
  let μ := (intervalStieltjes g hm hc).measure
  have hfinite : IsFiniteMeasure μ := intervalStieltjes_finite hm hc
  refine ⟨⟨μ, hfinite, intervalStieltjes_noAtoms hm hc,
    intervalStieltjes_compl hm hc, ?_, ?_⟩⟩
  · change 0 < (intervalStieltjes g hm hc).measure.real univ
    rw [intervalStieltjes_mass_real hm hc hg0]
    exact monotone_nonconstant_terminal_pos hm hg0 hn
  · intro j
    by_cases hj : j.val = n
    · have hj0 : n - j.val = 0 := by omega
      rw [hj0]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
        integral_const, smul_eq_mul, mul_one]
      change b j = (intervalStieltjes g hm hc).measure.real univ
      rw [intervalStieltjes_mass_real hm hc hg0]
      simpa only [hj] using (ht j).symm
    · have hjn : j.val < n := by omega
      let k := n - j.val - 1
      have hsum : j.val + k + 1 = n := by omega
      have hdiff : n - j.val = k + 1 := by omega
      have hi := source_jet_integral (f := f) j.val k
        (by simpa only [hsum] using hf)
        (fun i hi => h0 i (by omega))
      rw [hsum] at hi
      calc
        b j = ∫ t in (0 : ℝ)..1, ((1 - t) ^ k / (k.factorial : ℝ)) * g t :=
          (ht j).symm.trans hi
        _ = (∫ t in (0 : ℝ)..1, (1 - t) ^ k * g t) / (k.factorial : ℝ) := by
          rw [← intervalIntegral.integral_div]
          congr 1
          funext t
          ring
        _ = ((∫ t, (1 - t) ^ (k + 1) ∂μ) / (k + 1)) / (k.factorial : ℝ) := by
          rw [intervalStieltjes_kernel hm hc hg0 k]
        _ = (∫ t, (1 - t) ^ (n - j.val) ∂μ) / ((n - j.val).factorial : ℝ) := by
          rw [hdiff]
          simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_div]

end

end RepeatedIntegrals
