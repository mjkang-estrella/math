import SourceDefs
import Weights
import IntegerPolynomials

namespace Davis

def fallingCoeffs : ℕ → List ℤ
  | 0 => [1]
  | i + 1 => coeffMul (fallingCoeffs i) [-(i : ℤ), 1]

def scaledPCoeffs (d : ℕ) : List ℤ := coeffRangeSum (d + 1) fun i =>
  coeffScale (Nat.fast_choose d i) (coeffMul
    (coeffMul (fallingCoeffs i) (fallingCoeffs i))
    (coeffMul (fallingCoeffs (d - i)) (fallingCoeffs (d - i))))

def inequalityCoeffs (d : ℕ) : List ℤ :=
  coeffAdd
    (coeffMul
      (coeffAdd (coeffScale 200 (coeffMul [(d : ℤ) - 2, 2]
        [(d : ℤ) * (d + 1), -4 * d, 4])) [-398 * (d + 1 : ℤ) * (d - 2)])
      (scaledPCoeffs d))
    (coeffScale (-400) (coeffMul [(d : ℤ) - 2, 2] (scaledPCoeffs (d + 1))))

theorem coeffEval_falling (i : ℕ) (x : ℝ) : coeffEval (fallingCoeffs i) x = falling x i := by
  induction i with
  | zero => simp [fallingCoeffs, coeffEval, falling]
  | succ i ih =>
    rw [fallingCoeffs, coeffEval_mul, ih, falling_succ]
    simp only [coeffEval, Int.cast_neg, Int.cast_natCast, Int.cast_one, mul_zero, add_zero]
    ring

theorem coeffEval_scaledP (d : ℕ) (x : ℝ) :
    coeffEval (scaledPCoeffs d) x = (Nat.factorial d : ℝ) * P d x := by
  unfold scaledPCoeffs P
  rw [coeffEval_rangeSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hid : i ≤ d := by have := Finset.mem_range.mp hi; omega
  simp only [coeffEval_scale, coeffEval_mul, coeffEval_falling, Int.cast_natCast,
    ← Nat.choose_eq_fast_choose]
  have hc : (d.choose i : ℝ) * (Nat.factorial i : ℝ) *
      (Nat.factorial (d - i) : ℝ) = (Nat.factorial d : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hid
  have hf : (Nat.factorial i : ℝ) ≠ 0 := by positivity
  have hg : (Nat.factorial (d - i) : ℝ) ≠ 0 := by positivity
  unfold weight
  rw [← hc]
  field_simp

theorem coeffEval_inequality (d : ℕ) (x : ℝ) :
    coeffEval (inequalityCoeffs d) x = 400 * (d + 1 : ℝ) * (Nat.factorial d : ℝ) *
      (((2 * x + d - 2) * quotient d x - (199 / 200 : ℝ) * (d - 2)) * P d x -
       (2 * x + d - 2) * P (d + 1) x) := by
  have hd : (d + 1 : ℝ) ≠ 0 := by positivity
  simp only [inequalityCoeffs, coeffEval_add, coeffEval_mul, coeffEval_scale,
    coeffEval_scaledP, coeffEval, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat,
    Int.cast_mul, Int.cast_add, Int.cast_neg, mul_zero, add_zero,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  unfold quotient
  field_simp
  ring

end Davis
