import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
noncomputable section
open Finset Polynomial
namespace JacobiShifted
/-- Algebraic integration on polynomials in `u²`; no analytic integration is used. -/
def oddIntegral : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun j => (LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight (1 / (2 * (j : ℚ) + 1)))
lemma oddIntegral_monomial (n : ℕ) (a : ℚ) :
    oddIntegral (monomial n a) = a / (2 * n + 1) := by
  simp [oddIntegral, Polynomial.lsum, Polynomial.sum_monomial_index, div_eq_mul_inv]
lemma oddIntegral_C_mul (a : ℚ) (p : ℚ[X]) : oddIntegral (C a * p) = a * oddIntegral p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
lemma oddIntegral_C_mul_X_pow (a : ℚ) (n : ℕ) :
    oddIntegral (C a * X ^ n) = a / (2 * n + 1) := by
  rw [C_mul_X_pow_eq_monomial, oddIntegral_monomial]
lemma oddIntegral_boundary (p : ℚ[X]) :
    oddIntegral (p + C 2 * X * derivative p) = p.eval 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [mul_add, map_add, eval_add] at *
    linear_combination hp + hq
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial]
    cases n with
    | zero => simp [oddIntegral, Polynomial.lsum]
    | succ n =>
      simp only [derivative_C_mul_X_pow, Nat.add_one_sub_one]
      have heq : C a * X ^ (n + 1) + C 2 * X * (C (a * ↑(n + 1)) * X ^ n) =
          C (a * (2 * (n + 1) + 1)) * X ^ (n + 1) := by
        simp only [Nat.cast_add, Nat.cast_one, map_mul, map_add, map_ofNat, map_one]
        rw [pow_succ]
        ring
      rw [heq, oddIntegral_C_mul_X_pow]
      simp only [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
      have hn : (2 * ((n + 1 : ℕ) : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
lemma oddIntegral_beta_recurrence (n : ℕ) :
    (2 * (n : ℚ) + 3) * oddIntegral ((1 - X) ^ (n + 1)) =
      2 * (n + 1) * oddIntegral ((1 - X) ^ n) := by
  have h := oddIntegral_boundary ((1 - X) ^ (n + 1))
  have hp : (1 - X : ℚ[X]) ^ (n + 1) + C 2 * X * derivative ((1 - X) ^ (n + 1)) =
      C (2 * (n : ℚ) + 3) * (1 - X) ^ (n + 1) -
      C (2 * ((n : ℚ) + 1)) * (1 - X) ^ n := by
    rw [derivative_pow_succ]
    simp only [derivative_sub, derivative_one, derivative_X, zero_sub]
    simp only [map_mul, map_add, map_ofNat, map_one]
    rw [pow_succ]
    ring
  rw [hp, map_sub, oddIntegral_C_mul, oddIntegral_C_mul] at h
  simp only [eval_pow, eval_sub, eval_one, eval_X, sub_self, zero_pow (Nat.succ_ne_zero n)] at h
  exact sub_eq_zero.mp h

lemma oddIntegral_one : oddIntegral 1 = 1 := by
  simpa using oddIntegral_C_mul_X_pow 1 0

lemma oddIntegral_binomial (p : ℚ[X]) (m : ℕ) :
    oddIntegral ((1 + p) ^ m) =
      ∑ k ∈ range (m + 1), (m.choose k : ℚ) * oddIntegral (p ^ k) := by
  rw [add_comm (1 : ℚ[X]) p, add_pow, map_sum]
  apply sum_congr rfl
  intro k _
  rw [one_pow, mul_one, ← C_eq_natCast, mul_comm, oddIntegral_C_mul]

lemma oddIntegral_one_add_X (m : ℕ) :
    oddIntegral ((1 + X) ^ m) =
      ∑ j ∈ range (m + 1), (m.choose j : ℚ) / (2 * j + 1) := by
  rw [oddIntegral_binomial]
  apply sum_congr rfl
  intro j _
  have h : oddIntegral (X ^ j) = 1 / (2 * j + 1) := by
    simpa using oddIntegral_C_mul_X_pow 1 j
  rw [h, mul_one_div]

lemma oddIntegral_neg_binomial (p : ℚ[X]) (m : ℕ) :
    oddIntegral ((1 - p) ^ m) =
      ∑ k ∈ range (m + 1), (-1 : ℚ) ^ k * (m.choose k : ℚ) * oddIntegral (p ^ k) := by
  rw [sub_eq_add_neg, oddIntegral_binomial]
  apply sum_congr rfl
  intro k _
  rw [neg_pow]
  have he : (-1 : ℚ[X]) ^ k = C ((-1 : ℚ) ^ k) := by simp
  rw [he, oddIntegral_C_mul]
  ring

end JacobiShifted
