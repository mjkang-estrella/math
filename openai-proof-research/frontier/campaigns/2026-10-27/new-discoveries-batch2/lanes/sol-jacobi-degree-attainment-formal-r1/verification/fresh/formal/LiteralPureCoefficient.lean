import PurePrimitive
import LogRiccatiIdentification

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section
namespace JacobiShifted.SourceBridge
open MidpointRational

/-- The two Riccati phases combine to a single minus sign at positive odd order. -/
theorem odd_sign_product (r : ℕ) (hr : 1≤r) :
    (-1 : ℚ)^r*(-1 : ℚ)^(r-1)= -1 := by
  rw [← pow_add, show r+(r-1)=2*(r-1)+1 by omega, pow_succ, pow_mul]
  norm_num

/-- Closed derivative of the pure-u coefficient of the actual finite logarithm. -/
theorem literal_pure_derivative (r : ℕ) (hr : 1≤r) :
    delta ((L (2*r-1)).im.coeff (Finsupp.single 0 r))=
      -rationalBase ((catalan (r-1) : ℚ)/(2 : ℚ)^r)*(w*t)^r := by
  rw [imaginary_logarithmic_derivative_odd_coeff r hr, scaledH_odd_pure_u r hr]
  have hs : (-1 : QAlg)^r=rationalBase ((-1 : ℚ)^r) := by simp
  rw [hs, ← mul_assoc, ← map_mul]
  have hc : (-1 : ℚ)^r*((-1 : ℚ)^(r-1)*(catalan (r-1) : ℚ)/2^r)=
      -((catalan (r-1) : ℚ)/2^r) := by
    calc
      _ = ((-1 : ℚ)^r*(-1 : ℚ)^(r-1))*((catalan (r-1) : ℚ)/2^r) := by ring
      _ = _ := by rw [odd_sign_product r hr]; ring
  rw [hc,map_neg]

/-- Primitive uniqueness identifies the literal source coefficient, with no
primitive or logarithmic-identification premises left over. -/
theorem literal_pure_primitive (r : ℕ) (hr : 1≤r) :
    (L (2*r-1)).im.coeff (Finsupp.single 0 r)=purePrimitive r := by
  apply normalized_unique
  · rw [literal_pure_derivative r hr,delta_purePrimitive r hr]
  · have hn := congrArg (fun p : A => p.coeff (Finsupp.single 0 r))
      (literal_imaginary_normalization (2*r-1)).1
    simpa only [tauA,MvPolynomial.coeff_map,MvPolynomial.coeff_neg] using hn
  · exact tau_purePrimitive r

/-- Exact midpoint value of the literal finite source logarithm at the pure-u
monomial. -/
theorem sourceLogCoeff_pure_u (r : ℕ) (hr : 1≤r) :
    (sourceLogCoeff (2*r-1)).im.coeff (Finsupp.single 0 r)=
      (catalan (r-1) : ℚ)*binomialOddSum (r-1)/(2 : ℚ)^(2*r-1) := by
  have he := congrArg (fun p : JacobiShifted.QPoly => p.coeff (Finsupp.single 0 r))
    (literal_imaginary_normalization (2*r-1)).2
  simp only [midpointA,MvPolynomial.coeff_map] at he
  rw [literal_pure_primitive r hr, midpoint_purePrimitive r hr] at he
  exact he.symm

/-- Mandatory literal endpoint: the unmodified finite definition of sourceKappa
has the stated Catalan/binomial coefficient at every positive order. -/
theorem sourceKappa_pure_u (r : ℕ) (hr : 1≤r) :
    (sourceKappa r).coeff (Finsupp.single 0 r)=
      (catalan (r-1) : ℚ)*binomialOddSum (r-1)/(2 : ℚ)^(4*r-2) := by
  rw [sourceKappa, ite_eq_right (by omega : r≠0), MvPolynomial.coeff_C_mul,
    sourceLogCoeff_pure_u r hr]
  rw [show 4*r-2=(2*r-1)+(2*r-1) by omega, pow_add]
  ring

end JacobiShifted.SourceBridge
