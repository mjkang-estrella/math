import Std

namespace Factoring

/-- Pointwise conservation of the integer error after removing the exact
reciprocal component. A, B, C are evaluations, not unpriced polynomial oracles.
This proves no error bound, coverage, search algorithm, or complexity result. -/
theorem residual_normalization_error {N p q A B C b : Int}
    (hN : N = p * q) (hB : B = p * C + b) :
    A - B * q = (A - N * C) - b * q := by
  grind

/-- Normalization preserves the recovery equation at every integer x,
without assuming that x is a factor. -/
theorem residual_normalization_recovery {N x A B C b e : Int}
    (hB : B = x * C + b) :
    x * (A - e) - N * B = x * ((A - N * C) - e) - N * b := by
  grind

/-- At x=1 the same change preserves the public exponent used by the
hidden-period consumer. No modular exponentiation theorem is assumed here. -/
theorem residual_normalization_exponent {N A B C b : Int}
    (hB : B = C + b) :
    A - N * B = (A - N * C) - N * b := by
  grind

/-- A nonzero constant denominator makes the recovery expression nonzero
at zero. For a polynomial expression, this excludes the zero polynomial. -/
theorem residual_recovery_nonzero_at_zero {N b : Int}
    (hN : N ≠ 0) (hb : b ≠ 0) (A e : Int) :
    0 * (A - e) - N * b ≠ 0 := by
  have h := Int.mul_ne_zero hN hb
  simpa using h

/-- The exact rational reciprocal A=N, B=x supplies only the zero recovery
expression at error zero. Exact approximation alone need not reveal a factor. -/
theorem exact_reciprocal_recovery_zero (N x : Int) :
    x * (N - 0) - N * x = 0 := by
  grind

end Factoring
