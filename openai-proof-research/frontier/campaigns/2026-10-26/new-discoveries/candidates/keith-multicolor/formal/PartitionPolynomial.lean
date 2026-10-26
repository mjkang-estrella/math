import PartitionSource

namespace KeithMulticolor

/-- The literal three-color counting polynomial after setting x3=1. Each
distinct size independently chooses color x, color y, or the third color. -/
noncomputable def sourcePolynomial (N n : ℕ) : Polynomial (Polynomial ℕ) :=
  ∑ p ∈ squareBox N n,
    (Polynomial.X + Polynomial.C (Polynomial.X + 1)) ^ distinctCount p

theorem colorPolynomial_coefficient (r i j : ℕ) :
    (((Polynomial.X + Polynomial.C (Polynomial.X + 1)) ^ r :
      Polynomial (Polynomial ℕ)).coeff i).coeff j =
        r.choose i * (r - i).choose j := by
  rw [Polynomial.coeff_X_add_C_pow, ← Polynomial.C_eq_natCast,
    Polynomial.coeff_mul_C, Polynomial.coeff_X_add_one_pow]
  simp [mul_comm]

theorem sourcePolynomial_coefficient (N n i j : ℕ) :
    ((sourcePolynomial N n).coeff i).coeff j = sourceArray N n i j := by
  classical
  simp only [sourcePolynomial, sourceArray, Polynomial.finsetSum_coeff,
    colorPolynomial_coefficient]

end KeithMulticolor
