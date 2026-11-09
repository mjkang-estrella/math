import PolynomialConvexity.Layercake
import Mathlib.MeasureTheory.Integral.Pi

namespace PolynomialConvexity
noncomputable section
open MeasureTheory ProbabilityTheory Set

theorem positive_rate_integral (a : ℝ) (ha : 0 < a) :
    (∫ u : ℝ in Ioi 0, Real.exp (-(a*u))) = a⁻¹ := by
  simpa only [neg_mul, mul_zero, Real.exp_zero, neg_div_neg_eq, one_div] using
    integral_exp_mul_Ioi (a := -a) (neg_neg_of_pos ha) 0

theorem gap_integral (d : ℕ) (a : Fin d → ℝ) (ha : ∀ j, 0 < a j) :
    (∫ u : Fin d → ℝ in Set.pi Set.univ (fun _ => Ioi (0 : ℝ)),
      Real.exp (-∑ j, a j * u j)) = ∏ j, (a j)⁻¹ := by
  rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  simp_rw [← Finset.sum_neg_distrib, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun j u => Real.exp (-(a j*u)))]
  exact Finset.prod_congr rfl (fun j _ => positive_rate_integral (a j) (ha j))

theorem gap_integrable (d : ℕ) (a : Fin d → ℝ) (ha : ∀ j, 0 < a j) :
    IntegrableOn (fun u : Fin d → ℝ => Real.exp (-∑ j, a j * u j))
      (Set.pi Set.univ (fun _ => Ioi (0 : ℝ))) := by
  unfold IntegrableOn
  rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  simp_rw [← Finset.sum_neg_distrib, Real.exp_sum]
  exact Integrable.fintype_prod (fun j => by
    simpa only [IntegrableOn, neg_mul] using integrableOn_exp_mul_Ioi (a := -a j) (neg_neg_of_pos (ha j)) 0)

theorem prefix_gap_integral {n L d : ℕ} (hL : 0 < L) (e : Fin d → Edge n L) :
    (∫ u : Fin d → ℝ in Set.pi Set.univ (fun _ => Ioi (0 : ℝ)),
      Real.exp (-∑ j, ((prefixUnion e j).card : ℝ) * u j)) = coefficient e := by
  exact gap_integral d _ (fun j => Nat.cast_pos.mpr (prefix_card_pos hL e j))

end
end PolynomialConvexity
