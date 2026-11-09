import UlasChecks
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open PowerSeries
namespace Ulas
/-- Closed coefficient polynomials, proved by multiplication rather than interpolation. -/
theorem q_pow_low (m : ℕ) :
    (q^m).coeff 0 = 1 ∧
    (q^m).coeff 1 = 2*(m:ℤ) ∧
    (q^m).coeff 2 = 2*(m:ℤ)*((m:ℤ)+1) ∧
    3*(q^m).coeff 3 = 4*(m:ℤ)^3+12*(m:ℤ)^2+2*(m:ℤ) ∧
    3*(q^m).coeff 4 = 2*(m:ℤ)^4+12*(m:ℤ)^3+10*(m:ℤ)^2+6*(m:ℤ) := by
  induction m with
  | zero => norm_num [Polynomial.coeff_one]
  | succ m ih =>
    rcases ih with ⟨h0,h1,h2,h3,h4⟩
    have conv (n : ℕ) : (q^(m+1)).coeff n =
        ∑ x ∈ Finset.antidiagonal n, (q^m).coeff x.1 * q.coeff x.2 := by
      rw [pow_succ, Polynomial.coeff_mul]
    constructor
    · simpa [conv, Finset.Nat.antidiagonal_zero, qc_0] using h0
    constructor
    · norm_num [conv, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        qc_0, qc_1, h0, h1]
      ring
    constructor
    · norm_num [conv, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        qc_0, qc_1, qc_2, h0, h1, h2]
      ring
    constructor
    · norm_num [conv, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        qc_0, qc_1, qc_2, qc_3, h0, h1, h2]
      linear_combination h3
    · norm_num [conv, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        qc_0, qc_1, qc_2, qc_3, qc_4, h0, h1, h2]
      linear_combination h4 + 2*h3

/-- Universal n=1 difference; denominators are cleared over the integers. -/
theorem diff_one_polynomial (m : ℕ) :
    3 * diff m 1 = 2*(m:ℤ)^2*((m:ℤ)+1)*((m:ℤ)+5) := by
  rw [diff, c_low m 4 (by omega), c_low m 1 (by omega)]
  obtain ⟨_,h1,_,_,h4⟩ := q_pow_low m
  rw [h1]
  linear_combination h4
end Ulas
