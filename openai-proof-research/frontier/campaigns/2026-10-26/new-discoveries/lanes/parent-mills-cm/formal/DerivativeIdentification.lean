import DerivativeRecurrence
import DerivativeTable

open scoped BigOperators
open Polynomial

namespace MillsCounterexample

theorem mills_derivative_poly (n : ℕ) : iteratedDeriv n mills 0 =
    (millsDerivativePoly n).eval₂ (Int.castRingHom ℝ) (mills 0) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [millsDerivativePoly, iteratedDeriv_zero]
  | one => simp [millsDerivativePoly, iteratedDeriv_one, mills_deriv]
  | more n hn _ =>
      rw [mills_derivative_succ_succ, hn]
      simp [millsDerivativePoly, Polynomial.eval₂_mul]

theorem quotient_derivative_poly (n : ℕ) (hn : n ≤ 40) : iteratedDeriv n quotient 0 =
    (ratioDerivativePoly n).eval₂ (Int.castRingHom ℝ) (mills 0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [quotient_zero, iteratedDeriv_zero, ratioDerivativePoly_zero]
      | succ n =>
          have hp := ratioDerivativePoly_step ⟨n, by omega⟩
          change ratioDerivativePoly (n + 1) = _ at hp
          rw [quotient_derivative_recurrence, hp]
          simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum,
            Polynomial.eval₂_mul, Polynomial.eval₂_C, Int.coe_castRingHom, Int.cast_natCast]
          simp_rw [mills_derivative_poly]
          congr 1
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [ih (n - k) (by omega) (by omega)]

end MillsCounterexample
