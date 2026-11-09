import HalfSubstitution
import OddPrimitiveSequence
import LogRiccatiIdentification
import DyadicArithmetic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
noncomputable section
namespace JacobiShifted.SourceBridge
open BinaryFiltration MidpointRational

/-- Choose only from the already proved closed primitive existence theorem. -/
def coefficientPrimitive (n : ℕ) (hn : Odd n) (e : Exponent) : QAlg :=
  Classical.choose (h_odd_primitive_existsUnique n (e 0) (e 1) hn)

theorem coefficientPrimitive_spec (n : ℕ) (hn : Odd n) (e : Exponent) :
    delta (coefficientPrimitive n hn e) = lift ((Midpoint.h n).coeff e) ∧
      tau (coefficientPrimitive n hn e) = -coefficientPrimitive n hn e := by
  have h := (Classical.choose_spec (h_odd_primitive_existsUnique n (e 0) (e 1) hn)).1
  simpa only [coefficientPrimitive, ← exponent_bidegree] using h

theorem coefficientPrimitive_bound (n : ℕ) (hn : Odd n) (e : Exponent) :
    MidpointRational.TwoLocal
      (midpoint (coefficientPrimitive n hn e) / (2 : ℚ)^sigma (e.degree-1)) := by
  have h := coefficientPrimitive_spec n hn e
  have hd : delta (coefficientPrimitive n hn e) =
      lift ((Midpoint.h n).coeff (bidegree (e 0) (e 1))) := by
    simpa only [← exponent_bidegree] using h.1
  simpa only [ParameterDegree.exponent_degree] using
    h_odd_primitive_midpoint n (e 0) (e 1) hn _ hd h.2

theorem odd_source_index (r : ℕ) (hr : 1 ≤ r) : Odd (2*r-1) := by
  exact ⟨r-1, by omega⟩

def transportedPrimitive (r : ℕ) (hr : 1 ≤ r) (m : Exponent) : QAlg :=
  ∑ e ∈ (Midpoint.h (2*r-1)).support,
    rationalBase ((-1 : ℚ)^r * substitutionWeight e m) *
      coefficientPrimitive (2*r-1) (odd_source_index r hr) e

theorem delta_transportedPrimitive (r : ℕ) (hr : 1 ≤ r) (m : Exponent) :
    delta (transportedPrimitive r hr m) =
      (-1 : QAlg)^r * (scaledH (2*r-1)).coeff m := by
  classical
  simp only [transportedPrimitive, map_sum, partial_mul, delta_rationalBase,
    zero_mul, zero_add, (coefficientPrimitive_spec _ _ _).1]
  rw [scaledH, scale_coeff_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_mul, map_pow, map_neg, map_one]
  ring

theorem tau_transportedPrimitive (r : ℕ) (hr : 1 ≤ r) (m : Exponent) :
    tau (transportedPrimitive r hr m) = -transportedPrimitive r hr m := by
  classical
  simp only [transportedPrimitive, map_sum, map_mul, tau_rationalBase,
    (coefficientPrimitive_spec _ _ _).2, mul_neg, Finset.sum_neg_distrib]

theorem literal_transportedPrimitive (r : ℕ) (hr : 1 ≤ r) (m : Exponent) :
    (L (2*r-1)).im.coeff m = transportedPrimitive r hr m := by
  apply normalized_unique
  · rw [imaginary_logarithmic_derivative_odd_coeff r hr, delta_transportedPrimitive r hr]
  · have h := congrArg (fun p : A => p.coeff m)
      (literal_imaginary_normalization (2*r-1)).1
    simpa only [tauA, MvPolynomial.coeff_map, MvPolynomial.coeff_neg] using h
  · exact tau_transportedPrimitive r hr m

theorem sourceKappa_coeff_expansion (r : ℕ) (hr : 1 ≤ r) (m : Exponent) :
    (sourceKappa r).coeff m = ((2 : ℚ)^(2*r-1))⁻¹ *
      ∑ e ∈ (Midpoint.h (2*r-1)).support,
        ((-1 : ℚ)^r * substitutionWeight e m) *
          midpoint (coefficientPrimitive (2*r-1) (odd_source_index r hr) e) := by
  classical
  rw [sourceKappa, ite_eq_right (by omega : r≠0), MvPolynomial.coeff_C_mul]
  have h := congrArg (fun p : JacobiShifted.QPoly => p.coeff m)
    (literal_imaginary_normalization (2*r-1)).2
  simp only [midpointA, MvPolynomial.coeff_map] at h
  rw [← h, literal_transportedPrimitive r hr, transportedPrimitive]
  simp only [map_sum, map_mul, midpoint_rationalBase]

theorem twoLocal_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, MidpointRational.TwoLocal (f i)) :
    MidpointRational.TwoLocal (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact twoLocal_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact twoLocal_add (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem power_balance (E n d s k : ℕ) (h : E+s=n+d+k) :
    (2 : ℚ)^E * ((2 : ℚ)^n)⁻¹ / (2 : ℚ)^d =
      (2 : ℚ)^k / (2 : ℚ)^s := by
  have hp : (2 : ℚ)^E * 2^s = 2^n * 2^d * 2^k := by
    rw [← pow_add, ← pow_add, ← pow_add, h]
  field_simp
  nlinarith [hp]

/-- Each support monomial pays its own half-substitution denominator. -/
theorem transported_term_twoLocal (r : ℕ) (hr : 1 ≤ r) (m e : Exponent)
    (he : e ∈ (Midpoint.h (2*r-1)).support) :
    MidpointRational.TwoLocal
      ((2 : ℚ)^dyadicExponent r * ((2 : ℚ)^(2*r-1))⁻¹ *
        (((-1 : ℚ)^r * substitutionWeight e m) *
          midpoint (coefficientPrimitive (2*r-1) (odd_source_index r hr) e))) := by
  have he0 : (Midpoint.h (2*r-1)).coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
  have hd : 1 ≤ e.degree := by
    by_contra hn
    have hz : e=0 := by
      ext i
      have hdeg := ParameterDegree.exponent_degree e
      fin_cases i <;> simp_all
    subst e
    have hz := h_zero_parameter (2*r-1)
    simp only [bidegree, Finsupp.single_zero, add_zero] at hz
    exact he0 hz
  have hdr : e.degree ≤ r := by
    have h : e.degree ≤ (2*r-1+1)/2 :=
      (MvPolynomial.le_totalDegree he).trans (ParameterDegree.h_totalDegree (2*r-1))
    omega
  let k := padicValNat 2 ((r-1).factorial) - padicValNat 2 ((e.degree-1).factorial)
  have hp := power_balance (dyadicExponent r) (2*r-1) e.degree
    (sigma (e.degree-1)) k (DyadicArithmetic.exponent_balance hd hdr)
  have hid : (2 : ℚ)^dyadicExponent r * ((2 : ℚ)^(2*r-1))⁻¹ *
      (((-1 : ℚ)^r * substitutionWeight e m) *
        midpoint (coefficientPrimitive (2*r-1) (odd_source_index r hr) e)) =
      (((-1 : ℚ)^r * ((substitutionNumerator e).coeff m : ℚ)) * (2 : ℚ)^k) *
        (midpoint (coefficientPrimitive (2*r-1) (odd_source_index r hr) e) /
          (2 : ℚ)^sigma (e.degree-1)) := by
    dsimp only [substitutionWeight]
    calc
      _ = ((-1 : ℚ)^r * ((substitutionNumerator e).coeff m : ℚ)) *
          ((2 : ℚ)^dyadicExponent r * ((2 : ℚ)^(2*r-1))⁻¹ / (2 : ℚ)^e.degree) *
          midpoint (coefficientPrimitive (2*r-1) (odd_source_index r hr) e) := by ring
      _ = _ := by rw [hp]; ring
  rw [hid]
  apply twoLocal_mul
  · exact twoLocal_mul
      (twoLocal_mul (by simpa using twoLocal_int ((-1 : ℤ)^r))
        (twoLocal_int _)) (by simpa using twoLocal_nat (2^k))
  · exact coefficientPrimitive_bound _ _ _

/-- The literal finite source has the uniform denominator upper bound. -/
theorem sourceKappa_twoLocal (r : ℕ) (hr : 1 ≤ r) (m : Exponent) :
    JacobiShifted.TwoLocal ((2 : ℚ)^dyadicExponent r * (sourceKappa r).coeff m) := by
  rw [sourceKappa_coeff_expansion r hr, ← mul_assoc, Finset.mul_sum]
  exact twoLocal_finset_sum _ _ (fun e he => transported_term_twoLocal r hr m e he)

end JacobiShifted.SourceBridge
