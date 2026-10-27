import HamiltonianPolynomial
import LogCoefficients

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open Matrix PowerSeries

variable {K : Type*} [Field K] [CharZero K]
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

theorem trace_all_orders (u v : n → K) (lam xi gamma : K)
    (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) (m : ℕ) (hm : 0 < m) :
    Matrix.trace (algebraicLax u v lam xi ^ m) =
      ∑ j ∈ Finset.range m, (m : K) / (j + 1 : K) * lam ^ (j + 1) *
        coeff m ((hamiltonianPolynomial u v gamma : PowerSeries K) ^ (j + 1)) := by
  have ht := traceLog_coefficient (algebraicLax u v lam xi) m hm
  rw [determinant_series_collapse u v lam xi gamma hcurve] at ht
  rw [coeff_negative_log _ (by rw [map_mul, hamiltonianPolynomial_constantCoeff]; simp)] at ht
  have hm0 : (m : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  rw [eq_div_iff hm0] at ht
  rw [← ht, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow, ← map_pow, coeff_C_mul]
  ring

end PeakonCoefficients
