import Curvature333569
import Diagonal333569

namespace MathDB333569
noncomputable section
open Set

def coefficientTerm (l : ℝ) (n : ℕ) : ℝ :=
  (1/2:ℝ)^(n+1) * (transverseCoeff (l^(n+1)) - transverseCoeff l)

theorem coefficientTerm_nonpos {l : ℝ} (hl : l ∈ Ioo 0 1) (n : ℕ) :
    coefficientTerm l n ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (sub_nonpos.mpr (transverseCoeff_power_le hl (by omega)))

theorem coefficientTerm_bound {l : ℝ} (hl : l ∈ Ioo 0 1) (n : ℕ) :
    ‖coefficientTerm l n‖ ≤
      (1/2:ℝ)^(n+1) * (transverseCoeff l - transverseCoeff 0) := by
  have hp : l^(n+1) ∈ Ico (0:ℝ) 1 :=
    ⟨le_of_lt (pow_pos hl.1 _), pow_lt_one₀ (le_of_lt hl.1) hl.2 (by omega)⟩
  have hc := transverseCoeff_strictMonoOn.monotoneOn
    (show (0:ℝ) ∈ Ico 0 1 by constructor <;> norm_num) hp hp.1
  rw [Real.norm_eq_abs, abs_of_nonpos (coefficientTerm_nonpos hl n)]
  unfold coefficientTerm
  nlinarith [mul_nonneg (show 0 ≤ (1/2:ℝ)^(n+1) by positivity)
    (sub_nonneg.mpr hc)]

theorem coefficientTerm_summable {l : ℝ} (hl : l ∈ Ioo 0 1) :
    Summable (coefficientTerm l) := by
  have h : Summable (fun n : ℕ => (1/2:ℝ)^n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have h' : Summable (fun n : ℕ => (1/2:ℝ)^(n+1) *
      (transverseCoeff l-transverseCoeff 0)) := by
    simpa only [pow_succ, mul_assoc] using
      (h.mul_right (1/2)).mul_right (transverseCoeff l-transverseCoeff 0)
  exact h'.of_norm_bounded (coefficientTerm_bound hl)

/-- Strict negativity of the coefficient series. Identification with a derivative
of the source functional still requires the uniform differentiation bridge. -/
theorem coefficientSeries_neg {l : ℝ} (hl : l ∈ Ioo 0 1) :
    (∑' n : ℕ, coefficientTerm l n) < 0 := by
  have hs : coefficientTerm l 1 < 0 := by
    apply mul_neg_of_pos_of_neg (by positivity)
    exact sub_neg.mpr (transverseCoeff_square_lt hl)
  simpa using Summable.tsum_lt_tsum (coefficientTerm_nonpos hl) hs
    (coefficientTerm_summable hl) (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))

#print axioms coefficientTerm_summable
#print axioms coefficientSeries_neg
end
end MathDB333569
