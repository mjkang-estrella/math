import Std

namespace Factoring

/-- A square represented by the binary form gives the indicated conic point.
This is a pointwise identity, not a square-representation algorithm. -/
theorem square_form_conic_point {a b c u v w N : Int}
    (hN : N = a * c - b ^ 2)
    (hw : a * u ^ 2 + 2 * b * u * v + c * v ^ 2 = w ^ 2) :
    (a * u + b * v) ^ 2 + N * v ^ 2 = a * w ^ 2 := by
  grind

/-- Homogeneous rational-line parametrization preserves the conic norm
up to its explicit square scale. No division or root selection is hidden. -/
theorem conic_line_norm (N A B X Y : Int) :
    ((N * A ^ 2 - B ^ 2) * X - 2 * N * A * B * Y) ^ 2 +
      N * ((B ^ 2 - N * A ^ 2) * Y - 2 * A * B * X) ^ 2 =
    (B ^ 2 + N * A ^ 2) ^ 2 * (X ^ 2 + N * Y ^ 2) := by
  grind

/-- The cross numerator for the negative root is an explicit multiple of N.
Using this identity as a congruence of quotients requires unit denominators. -/
theorem conic_line_negative_cross (N A B X Y Z : Int) :
    ((N * A ^ 2 - B ^ 2) * X - 2 * N * A * B * Y) * Z +
      X * ((B ^ 2 + N * A ^ 2) * Z) =
    2 * N * A * Z * (A * X - B * Y) := by
  grind

/-- If the line denominator is N*k, the first coordinate has a common N.
This is exact cancellation data, not division by a nonunit modulo N. -/
theorem conic_line_cancel_x (N A k X Y : Int) :
    (N * A ^ 2 - (N * k) ^ 2) * X - 2 * N * A * (N * k) * Y =
    N * ((A ^ 2 - N * k ^ 2) * X - 2 * N * A * k * Y) := by
  grind

/-- Exact common-factor identity for the second conic coordinate. -/
theorem conic_line_cancel_y (N A k X Y : Int) :
    ((N * k) ^ 2 - N * A ^ 2) * Y - 2 * A * (N * k) * X =
    N * ((N * k ^ 2 - A ^ 2) * Y - 2 * A * k * X) := by
  grind

/-- Exact common-factor identity for the homogeneous denominator. -/
theorem conic_line_cancel_z (N A k Z : Int) :
    ((N * k) ^ 2 + N * A ^ 2) * Z =
    N * ((A ^ 2 + N * k ^ 2) * Z) := by
  grind

/-- After cancelling a common N, the positive-root cross numerator is
an explicit multiple of N. The modular unit and gcd cases are separate. -/
theorem conic_line_positive_cross (N A k X Y Z : Int) :
    ((A ^ 2 - N * k ^ 2) * X - 2 * N * A * k * Y) * Z -
      X * ((A ^ 2 + N * k ^ 2) * Z) =
    -2 * N * k * Z * (k * X + A * Y) := by
  grind

end Factoring
