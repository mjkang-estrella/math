import Coprimality

namespace ContactPilot
noncomputable section
open MvPolynomial
private abbrev a : Poly₂ := C Complex.I * (1-Z)
private abbrev b : Poly₂ := 1+Z
private abbrev c : Poly₂ := C Complex.I * (1-W)
private abbrev e : Poly₂ := 1+W
/-- Clearing factor (1+Z)^3 (1+W)^2, with no cancellation assumed. -/
def cayleyN : Poly₂ := b * (c*a-c*b-b*e) * (c*a+c*b-b*e)
def cayleyQ : Poly₂ := -c^2*a^3 + 2*c^2*a*b^2 + 4*c*a^2*b*e +
  2*c*a*b^2*e - c*b^3*e - 3*a*b^2*e^2
def bidiskNumerator : Poly₂ := cayleyQ + C Complex.I * cayleyN
def bidiskDenominator : Poly₂ := cayleyQ - C Complex.I * cayleyN

theorem eval_n (z w : ℂ) : eval₂ n z w = (w*z-w-1)*(w*z+w-1) := by
  simp [eval₂, n, factorMinus, factorPlus, Z, W]
theorem eval_q (z w : ℂ) : eval₂ q z w =
    -w^2*z^3+2*w^2*z+4*w*z^2+2*w*z-w-3*z := by
  simp [eval₂, q, Z, W]

theorem cayleyN_clearing (z w : ℂ) (hz : 1+z ≠ 0) (hw : 1+w ≠ 0) :
    eval₂ cayleyN z w = (1+z)^3*(1+w)^2 * eval₂ n (betaInv z) (betaInv w) := by
  rw [eval_n]
  simp only [cayleyN, a, b, c, e, eval₂, map_mul, map_sub, map_add,
    map_one, eval_C, eval_X, Z, W]
  norm_num only [Fin.isValue, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide]
  unfold betaInv
  field_simp [hz, hw]

theorem cayleyQ_clearing (z w : ℂ) (hz : 1+z ≠ 0) (hw : 1+w ≠ 0) :
    eval₂ cayleyQ z w = (1+z)^3*(1+w)^2 * eval₂ q (betaInv z) (betaInv w) := by
  rw [eval_q]
  simp only [cayleyQ, a, b, c, e, eval₂, map_mul, map_sub, map_add,
    map_neg, map_pow, map_ofNat, map_one, eval_C, eval_X, Z, W]
  norm_num only [Fin.isValue, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide]
  unfold betaInv
  field_simp [hz, hw]

theorem bidisk_boundary_zero :
    eval₂ bidiskNumerator (-1) 1 = 0 ∧ eval₂ bidiskDenominator (-1) 1 = 0 := by
  norm_num [bidiskNumerator, bidiskDenominator, cayleyN, cayleyQ, a, b, c, e,
    eval₂, Z, W]

theorem bidiskDenominator_ne_zero : bidiskDenominator ≠ 0 := by
  intro h
  have hv := congrArg (fun p : Poly₂ => eval₂ p 0 0) h
  norm_num [bidiskDenominator, cayleyN, cayleyQ, a, b, c, e, eval₂, Z, W,
    Complex.I_sq, Complex.ext_iff, map_ofNat] at hv

theorem bidisk_represents_quotient (z w : ℂ) (hz : 1+z ≠ 0) (hw : 1+w ≠ 0)
    (hq : eval₂ q (betaInv z) (betaInv w) ≠ 0) :
    beta (eval₂ n (betaInv z) (betaInv w) / eval₂ q (betaInv z) (betaInv w)) =
      eval₂ bidiskNumerator z w / eval₂ bidiskDenominator z w := by
  have ht : (1+z)^3 * (1+w)^2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ hw)
  have evadd : eval₂ bidiskNumerator z w = eval₂ cayleyQ z w + Complex.I * eval₂ cayleyN z w := by
    simp [bidiskNumerator, eval₂]
  have evsub : eval₂ bidiskDenominator z w = eval₂ cayleyQ z w - Complex.I * eval₂ cayleyN z w := by
    simp [bidiskDenominator, eval₂]
  rw [evadd, evsub]
  rw [cayleyN_clearing z w hz hw, cayleyQ_clearing z w hz hw]
  unfold beta
  rw [show (1+z)^3*(1+w)^2 * eval₂ q (betaInv z) (betaInv w) +
      Complex.I*((1+z)^3*(1+w)^2 * eval₂ n (betaInv z) (betaInv w)) =
      ((1+z)^3*(1+w)^2) * (eval₂ q (betaInv z) (betaInv w) +
      Complex.I*eval₂ n (betaInv z) (betaInv w)) by ring,
    show (1+z)^3*(1+w)^2 * eval₂ q (betaInv z) (betaInv w) -
      Complex.I*((1+z)^3*(1+w)^2 * eval₂ n (betaInv z) (betaInv w)) =
      ((1+z)^3*(1+w)^2) * (eval₂ q (betaInv z) (betaInv w) -
      Complex.I*eval₂ n (betaInv z) (betaInv w)) by ring,
    mul_div_mul_left _ _ ht]
  simp only [← mul_div_assoc]
  rw [one_add_div hq, one_sub_div hq, div_div_div_cancel_right₀ hq]

theorem cleared_pair_reduced : ∀ d : Poly₂,
    d ∣ (q + C Complex.I*n) → d ∣ (q - C Complex.I*n) → IsUnit d := by
  intro d hp hm
  have hq : d ∣ q := by
    have h := dvd_add hp hm
    have he : (q + C Complex.I*n) + (q - C Complex.I*n) = q * 2 := by ring
    rw [he] at h
    have hu : IsUnit (2 : Poly₂) := by
      exact (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).map C
    exact hu.dvd_mul_right.mp h
  have hn : d ∣ n := by
    have h := dvd_sub hp hm
    have he : (q + C Complex.I*n) - (q - C Complex.I*n) = n * C (2*Complex.I) := by
      simp only [map_mul, map_ofNat]; ring
    rw [he] at h
    have hu : IsUnit (C (2*Complex.I) : Poly₂) :=
      (isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) Complex.I_ne_zero)).map C
    exact hu.dvd_mul_right.mp h
  exact numerator_denominator_reduced d hn hq
end
end ContactPilot
