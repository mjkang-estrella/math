import Std

namespace Factoring

/-- Exact integer data for the reciprocal certificates in H012.
The witnesses make integrality explicit; no shortness or coverage is assumed. -/
structure ReciprocalCertificate (N m j : Int) where
  u : Int
  v : Int
  t : Int
  slope : Int
  constant : Int
  slope_eq : v + 2 * u * j = m * slope
  constant_eq : N * t + u * j * j + v * j = m * m * constant
  informative : u ≠ 0 ∨ t ≠ 0

def ReciprocalCertificate.eval {N m j : Int}
    (c : ReciprocalCertificate N m j) (x : Int) : Int :=
  c.u * x * x + c.slope * x + c.constant

/-- The certificate gives an integer polynomial after division by m squared. -/
theorem certificate_evaluation {N m j : Int}
    (c : ReciprocalCertificate N m j) (x : Int) :
    m * m * c.eval x =
      c.u * (m * x + j) * (m * x + j) + c.v * (m * x + j) + N * c.t := by
  have hs := c.slope_eq
  have hc := c.constant_eq
  grind [ReciprocalCertificate.eval]

/-- At a factor in the represented residue class, coprimality permits cancelling
p from the divisibility identity. This establishes existence, not search cost. -/
theorem certificate_quotient_exists {N m j p q x : Int}
    (c : ReciprocalCertificate N m j) (hN : N = p * q)
    (hp : p = m * x + j) (hcop : Int.gcd (m * m) p = 1) :
    ∃ i : Int, m * m * i = c.u * p + c.v + c.t * q := by
  have hd : m * m ∣ p * (c.u * p + c.v + c.t * q) := by
    refine ⟨c.eval x, ?_⟩
    have he := certificate_evaluation c x
    grind
  have hq : m * m ∣ c.u * p + c.v + c.t * q := by
    have h := Int.dvd_gcd_mul_iff_dvd_mul.mpr hd
    simpa [hcop] using h
  obtain ⟨i, hi⟩ := hq
  exact ⟨i, hi.symm⟩

/-- A known integer quotient supplies the quadratic recovery equation.
This proves an algebraic implication, not how to find the quotient. -/
theorem quotient_recovery {N m u v t p q i : Int}
    (hN : N = p * q) (hi : m * m * i = u * p + v + t * q) :
    u * p * p + (v - i * m * m) * p + t * N = 0 := by
  grind

/-- For nonzero p, the recovery equation is equivalent to the exact quotient.
An arbitrary modular exponent collision alone is not this premise. -/
theorem recovery_iff_quotient {N m u v t p q i : Int}
    (hN : N = p * q) (hp : p ≠ 0) :
    u * p * p + (v - i * m * m) * p + t * N = 0 ↔
      m * m * i = u * p + v + t * q := by
  constructor
  · intro h
    have hz : p * (u * p + v + t * q - m * m * i) = 0 := by
      grind
    have hq := (Int.mul_eq_zero.mp hz).resolve_left hp
    omega
  · exact quotient_recovery hN

/-- Excluding the constant-quotient direction prevents an identically zero
recovery polynomial for nonzero N. -/
theorem certificate_recovery_nonzero {N m j : Int}
    (c : ReciprocalCertificate N m j) (hN : N ≠ 0) (i : Int) :
    c.u ≠ 0 ∨ c.v - i * m * m ≠ 0 ∨ c.t * N ≠ 0 := by
  rcases c.informative with hu | ht
  · exact Or.inl hu
  · exact Or.inr (Or.inr (Int.mul_ne_zero ht hN))

end Factoring
