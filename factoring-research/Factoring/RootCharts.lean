import Std

namespace Factoring

/-- The degree-four square-root series, scaled by 128 so it is integral. -/
def sqrtSeries4 (z : Int) : Int :=
  128 + 64 * z - 16 * z ^ 2 + 8 * z ^ 3 - 5 * z ^ 4

/-- The exact residual after squaring the scaled series. -/
theorem sqrt_series4_residual (z : Int) :
    (sqrtSeries4 z) ^ 2 - 16384 * (1 + z) =
      z ^ 5 * (25 * z ^ 3 - 80 * z ^ 2 + 224 * z - 896) := by
  unfold sqrtSeries4
  grind

/-- The total-degree-four part of 128 * sqrt(1+x) * sqrt(1+y).
This is an integer polynomial, not an analytic square-root operation. -/
def sqrtProduct4 (x y : Int) : Int :=
  128 + 64 * x + 64 * y - 16 * x ^ 2 + 32 * x * y - 16 * y ^ 2 +
    8 * x ^ 3 - 8 * x ^ 2 * y - 8 * x * y ^ 2 + 8 * y ^ 3 -
    5 * x ^ 4 + 4 * x ^ 3 * y + 2 * x ^ 2 * y ^ 2 +
    4 * x * y ^ 3 - 5 * y ^ 4

/-- Terms removed when two degree-four series are truncated by total degree. -/
def sqrtProduct4Tail (H x y : Int) : Int :=
  -320 * (x * y ^ 4 + x ^ 4 * y) -
    128 * (x ^ 2 * y ^ 3 + x ^ 3 * y ^ 2) +
    H * (80 * (x ^ 2 * y ^ 4 + x ^ 4 * y ^ 2) + 64 * x ^ 3 * y ^ 3) -
    40 * H ^ 2 * (x ^ 3 * y ^ 4 + x ^ 4 * y ^ 3) +
    25 * H ^ 3 * x ^ 4 * y ^ 4

/-- Truncation loses an explicit multiple of H^5, not arbitrary carries.
Using this modulo an odd prime power also needs unit denominators. -/
theorem sqrt_product4_truncation (H x y : Int) :
    sqrtSeries4 (H * x) * sqrtSeries4 (H * y) -
      128 * sqrtProduct4 (H * x) (H * y) =
    H ^ 5 * sqrtProduct4Tail H x y := by
  unfold sqrtSeries4 sqrtProduct4 sqrtProduct4Tail
  grind

/-- A ring identity propagating two square residuals and a product truncation.
No modular inverse or prime-power root acquisition is assumed here. -/
theorem truncated_product_square_residual
    (U V P c a b h e f t : Int)
    (hU : U ^ 2 = c ^ 2 * a + h * e)
    (hV : V ^ 2 = c ^ 2 * b + h * f)
    (hP : c * P = U * V - h * t) :
    c ^ 2 * (P ^ 2 - c ^ 2 * a * b) =
      h * (c ^ 2 * a * f + c ^ 2 * b * e + h * e * f -
        2 * t * U * V + h * t ^ 2) := by
  grind

/-- The covered exponent is an annihilator multiple with an explicit
residual modulo the public chart prime. Primality and units are separate. -/
theorem covered_exponent_residual (p q u v : Int) :
    u + (p * q) * v - (u * p + v * q) =
      u * (p - 1) ^ 2 - (p - 1) * (u * p - v * q) := by
  grind

/-- Propagate a public divisibility premise to the exponent residue.
This is an integer statement; it does not acquire a covered pair. -/
theorem covered_exponent_residue_dvd (p q u v ell : Int)
    (h : ell ∣ u * p - v * q) :
    ell ∣ (u + (p * q) * v - (u * p + v * q)) -
      u * (p - 1) ^ 2 := by
  rcases h with ⟨t, ht⟩
  refine ⟨-(p - 1) * t, ?_⟩
  grind

/-- The two sign residues multiply to the public line residual, up to
the supplied root residual. This does not assume a root modulo N. -/
theorem chart_sign_product_residual (u v n r : Int) :
    (u + n * v - r) * (u + n * v + r) =
      (u - n * v) ^ 2 + (4 * n * u * v - r ^ 2) := by
  grind

end Factoring
