import RiccatiScale
import ParameterDegree

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
noncomputable section
namespace JacobiShifted.SourceBridge
open BinaryFiltration

/-- The numerator of the half substitution is an actual integer polynomial. -/
def substitutionNumerator (e : Exponent) : MvPolynomial (Fin 2) ℤ :=
  (MvPolynomial.X 0 + MvPolynomial.X 1)^(e 0) *
    (MvPolynomial.X 0 - MvPolynomial.X 1)^(e 1)

def substitutionWeight (e m : Exponent) : ℚ :=
  ((substitutionNumerator e).coeff m : ℚ) / (2 : ℚ)^e.degree

theorem exponent_bidegree (e : Exponent) : e = bidegree (e 0) (e 1) := by
  ext i
  fin_cases i <;> simp [bidegree]

theorem scale_monomial (e : Exponent) (z : Midpoint.R) :
    scale (MvPolynomial.monomial e z) =
      MvPolynomial.C (MidpointRational.lift z) *
      MvPolynomial.C (rationalBase ((2 : ℚ)^e.degree)⁻¹) *
      MvPolynomial.map (rationalBase.comp (Int.castRingHom ℚ)) (substitutionNumerator e) := by
  classical
  have hh : ((2 : ℚ)^e.degree)⁻¹ = (1/2 : ℚ)^(e 0) * (1/2 : ℚ)^(e 1) := by
    rw [ParameterDegree.exponent_degree, pow_add]
    simp only [mul_inv, ← inv_pow, one_div]
  rw [scale, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype]
  · rw [hh]
    simp [Fin.prod_univ_two, subVar, substitutionNumerator,
      rationalScalar, paramEmbed, mul_pow]
    simp only [← inv_pow, map_pow, MvPolynomial.C_pow]
    ring
  · intro i; simp

theorem scale_coeff_expansion (f : Midpoint.Param) (m : Exponent) :
    (scale f).coeff m = ∑ e ∈ f.support,
      rationalBase (substitutionWeight e m) * MidpointRational.lift (f.coeff e) := by
  classical
  conv_lhs => rw [f.as_sum]
  simp only [map_sum, MvPolynomial.coeff_sum, scale_monomial]
  apply Finset.sum_congr rfl
  intro e _
  rw [mul_assoc, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  change MidpointRational.lift (f.coeff e) * (rationalBase (((2 : ℚ)^e.degree)⁻¹) *
    rationalBase ((substitutionNumerator e).coeff m : ℚ)) = _
  simp only [substitutionWeight, div_eq_mul_inv, map_mul]
  ring

end JacobiShifted.SourceBridge
