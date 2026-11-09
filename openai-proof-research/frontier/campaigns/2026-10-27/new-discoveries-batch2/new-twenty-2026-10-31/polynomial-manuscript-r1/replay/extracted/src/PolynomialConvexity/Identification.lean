import PolynomialConvexity.GapDomain
import PolynomialConvexity.Factored
set_option Elab.async false
namespace PolynomialConvexity
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

/-- Each actual labelled chamber contributes the literal prefix coefficient. -/
theorem chamber_integral {n L d : ℕ} (hL : 0 < L) (e : Fin d → Edge n L)
    (σ : Equiv.Perm (Fin d)) :
    (∫⁻ t in chamber σ, ENNReal.ofReal (Real.exp (-∑ v, vertexThreshold e t v))) =
      ENNReal.ofReal (coefficient (tuplePerm σ e)) := by
  rw [← (labelledGap_measurePreserving σ).setLIntegral_comp_preimage_emb
    (labelledGapEquiv σ).measurableEmbedding, labelledGap_preimage_chamber]
  calc
    _ = ∫⁻ u : Fin d → ℝ in Set.pi Set.univ (fun _ => Ioi (0 : ℝ)),
        ENNReal.ofReal (Real.exp (-∑ j, ((prefixUnion (tuplePerm σ e) j).card : ℝ) * u j)) := by
      apply setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)
      intro u hu
      dsimp only
      rw [labelledGapEquiv_apply, labelled_prefix_exponent e σ u
        (fun j => (hu j (mem_univ _)).le)]
    _ = ENNReal.ofReal (coefficient (tuplePerm σ e)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (gap_integrable d _ (fun j => Nat.cast_pos.mpr (prefix_card_pos hL _ j)))
        (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
      rw [prefix_gap_integral hL]

/-- Universal positive-orthant bridge, without any assumed moments or Jacobians. -/
theorem threshold_integral {n L d : ℕ} (hL : 0 < L) (e : Fin d → Edge n L) :
    (∫⁻ t : Fin d → ℝ in Set.pi Set.univ (fun _ => Ioi (0 : ℝ)),
      ENNReal.ofReal (Real.exp (-∑ v, vertexThreshold e t v))) =
      ENNReal.ofReal (symCoefficient e) := by
  rw [chamber_lintegral_partition]
  simp_rw [chamber_integral hL]
  exact (ENNReal.ofReal_sum_of_nonneg (fun σ _ => (coefficient_pos hL (tuplePerm σ e)).le)).symm

/-- The missing concrete mixed-moment identity, including repetitions. -/
theorem mixed_moment {n L d : ℕ} (hL : 0 < L) (e : Fin d → Edge n L) :
    (∫ ω, ∏ i, lifetime hL (e i) ω ∂clockMeasure n) = symCoefficient e := by
  have ha : 0 ≤ ∫ ω, ∏ i, lifetime hL (e i) ω ∂clockMeasure n :=
    integral_nonneg_of_ae ((clocks_nonneg n).mono fun ω hω =>
      Finset.prod_nonneg fun i _ => lifetime_nonneg hL (e i) ω hω)
  have hb : 0 ≤ symCoefficient e :=
    Finset.sum_nonneg fun σ _ => (coefficient_pos hL (tuplePerm σ e)).le
  have h := mixed_layercake hL e
  rw [threshold_integral hL] at h
  simpa only [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb] using congrArg ENNReal.toReal h

end
end PolynomialConvexity
