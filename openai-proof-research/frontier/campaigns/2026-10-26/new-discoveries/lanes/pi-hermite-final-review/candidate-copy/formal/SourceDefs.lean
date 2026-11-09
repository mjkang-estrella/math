import Mathlib

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

open Polynomial

/-- Physicists' normalization, matching Guo--Liu's Rodrigues definition. -/
def hermitePoly : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => C 2 * X * hermitePoly n - derivative (hermitePoly n)

def hermiteValue (n : ℕ) (x : ℝ) : ℝ := (hermitePoly n).eval x

def sourceHermite (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * Real.exp (x ^ 2) *
    (deriv^[n] (fun t : ℝ => Real.exp (-(t ^ 2)))) x

def weightedHermite (n : ℕ) (x : ℝ) : ℝ :=
  hermiteValue n x * Real.exp (-(x ^ 2) / 2)

def sourceCoefficient (n : ℕ) : ℝ :=
  2 ^ n * Real.Gamma (((n : ℝ) + 1) / 2) / Real.sqrt Real.pi

def sourceCutoff (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) + 1) *
    (1 - Real.pi / (2 * (2 * (n : ℝ) + 1)))

def sourceEnvelope (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt (1 - x ^ 2 / (2 * (n : ℝ) + 1)))⁻¹

def SourceConjecture346243 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
    |sourceHermite n x * Real.exp (-(x ^ 2))| ≤
      sourceCoefficient n * sourceEnvelope n (min x (sourceCutoff n)) *
        Real.exp (-(x ^ 2) / 2)

theorem hermitePoly_derivative_succ (n : ℕ) :
    derivative (hermitePoly (n + 1)) = C (2 * ((n : ℝ) + 1)) * hermitePoly n := by
  induction n with
  | zero => simp [hermitePoly]
  | succ n ih =>
    have hdd := congrArg derivative ih
    simp only [derivative_mul, derivative_C, zero_mul, zero_add] at hdd
    change derivative (C 2 * X * hermitePoly (n + 1) -
      derivative (hermitePoly (n + 1))) = _
    rw [derivative_sub, derivative_mul, derivative_mul, derivative_C,
      derivative_X, zero_mul, zero_add, mul_one, hdd, ih]
    rw [hermitePoly]
    push_cast
    simp only [map_add, map_mul, map_ofNat, map_one]
    ring

theorem hermitePoly_ode (n : ℕ) :
    derivative (derivative (hermitePoly n)) - C 2 * X * derivative (hermitePoly n) +
      C (2 * (n : ℝ)) * hermitePoly n = 0 := by
  cases n with
  | zero => simp [hermitePoly]
  | succ n =>
    rw [hermitePoly_derivative_succ]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add]
    rw [hermitePoly]
    push_cast
    simp only [map_add, map_mul, map_ofNat, map_one]
    ring

theorem gaussian_derivative (x : ℝ) :
    deriv (fun t : ℝ => Real.exp (-(t ^ 2))) x =
      -(2 * x) * Real.exp (-(x ^ 2)) := by
  convert (((hasDerivAt_id x).pow 2).neg.exp).deriv using 1 <;> simp [mul_comm]

theorem iterated_deriv_gaussian (n : ℕ) (x : ℝ) :
    (deriv^[n] (fun t : ℝ => Real.exp (-(t ^ 2)))) x =
      (-1 : ℝ) ^ n * hermiteValue n x * Real.exp (-(x ^ 2)) := by
  induction n generalizing x with
  | zero => simp [hermiteValue, hermitePoly]
  | succ n ih =>
    have ihf : deriv^[n] (fun t : ℝ => Real.exp (-(t ^ 2))) =
        fun t => (-1 : ℝ) ^ n * hermiteValue n t * Real.exp (-(t ^ 2)) := funext ih
    rw [Function.iterate_succ_apply', ihf]
    have hd : DifferentiableAt ℝ (hermiteValue n) x := (hermitePoly n).differentiableAt
    have he : DifferentiableAt ℝ (fun t : ℝ => Real.exp (-(t ^ 2))) x := by fun_prop
    rw [show (fun t => (-1 : ℝ) ^ n * hermiteValue n t * Real.exp (-(t ^ 2))) =
      (fun t => (-1 : ℝ) ^ n * (hermiteValue n t * Real.exp (-(t ^ 2)))) by funext t; ring]
    rw [deriv_const_mul_field, deriv_fun_mul hd he, gaussian_derivative]
    rw [show deriv (hermiteValue n) x = (derivative (hermitePoly n)).eval x from
      (hermitePoly n).deriv]
    simp only [hermiteValue, hermitePoly, eval_sub, eval_mul, eval_C, eval_X, pow_succ]
    ring

theorem sourceHermite_eq_value (n : ℕ) (x : ℝ) :
    sourceHermite n x = hermiteValue n x := by
  rw [sourceHermite, iterated_deriv_gaussian]
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]; simp
  have he : Real.exp (x ^ 2) * Real.exp (-(x ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  calc
    _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        (Real.exp (x ^ 2) * Real.exp (-(x ^ 2))) * hermiteValue n x := by ring
    _ = _ := by rw [hs, he]; ring

end HermiteEnvelope
