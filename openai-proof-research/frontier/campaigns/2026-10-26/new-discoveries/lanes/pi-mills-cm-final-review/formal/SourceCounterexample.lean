import DerivativeIdentification
import SignBound

open Filter Set
open scoped Topology ContDiff

namespace MillsCounterexample

theorem quotient_derivative40_negative : iteratedDeriv 40 quotient 0 < 0 := by
  rw [quotient_derivative_poly 40 (by omega), witnessPoly_identity,
    Polynomial.eval₂_comp, Polynomial.eval₂_pow, Polynomial.eval₂_X, mills_zero_sq]
  exact witnessPoly_pi_negative

theorem quotient_derivative40_continuousAt : ContinuousAt (iteratedDeriv 40 quotient) 0 := by
  have hc := (quotient_contDiffAt_zero 40).continuousAt_iteratedFDeriv (k := 40) (by rfl)
  exact hc.eval_const (fun _ : Fin 40 => (1 : ℝ))

theorem quotient_positive_interval_counterexample :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Ioo (0 : ℝ) δ, iteratedDeriv 40 quotient x < 0 := by
  have he : ∀ᶠ x in 𝓝 (0 : ℝ), iteratedDeriv 40 quotient x < 0 :=
    quotient_derivative40_continuousAt.eventually_lt_const quotient_derivative40_negative
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, fun x hx => hh ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hx.1] using hx.2

theorem regular_positive_interval_counterexample :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Ioo (0 : ℝ) δ,
      deriv mills x < 0 ∧ iteratedDeriv 40 quotient x < 0 := by
  have hd : ∀ᶠ x in 𝓝 (0 : ℝ), deriv mills x < 0 :=
    (mills_contDiff_nat 1).continuous_deriv_one.continuousAt.eventually_lt_const
      (by simp [mills_deriv])
  have hf : ∀ᶠ x in 𝓝 (0 : ℝ), iteratedDeriv 40 quotient x < 0 :=
    quotient_derivative40_continuousAt.eventually_lt_const quotient_derivative40_negative
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp (hd.and hf)
  refine ⟨δ, hδ, fun x hx => hh ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hx.1] using hx.2

def SourceCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ioi (0 : ℝ)) ∧
    ∀ (n : ℕ) (x : ℝ), 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n f x

noncomputable def sourceRatio (n : ℕ) (x : ℝ) : ℝ :=
  -(iteratedDeriv n mills x) ^ 2 / iteratedDeriv (2 * n + 1) mills x

theorem sourceRatio_zero : sourceRatio 0 = quotient := by
  funext x
  simp [sourceRatio, quotient, iteratedDeriv_zero, iteratedDeriv_one]

theorem source_ratio_zero_positive_interval :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Ioo (0 : ℝ) δ, iteratedDeriv 40 (sourceRatio 0) x < 0 := by
  rw [sourceRatio_zero]
  exact quotient_positive_interval_counterexample

theorem source_ratio_zero_not_completely_monotone : ¬ SourceCompletelyMonotone (sourceRatio 0) := by
  obtain ⟨δ, hδ, hh⟩ := source_ratio_zero_positive_interval
  intro hc
  have hn := hh (δ / 2) ⟨by linarith, by linarith⟩
  have hp := hc.2 40 (δ / 2) (by linarith)
  norm_num at hp
  linarith

def SourceConjecture351688 : Prop := ∀ n : ℕ, SourceCompletelyMonotone (sourceRatio n)

theorem source_counterexample_351688 : ¬ SourceConjecture351688 := by
  intro h
  exact source_ratio_zero_not_completely_monotone (h 0)

end MillsCounterexample
