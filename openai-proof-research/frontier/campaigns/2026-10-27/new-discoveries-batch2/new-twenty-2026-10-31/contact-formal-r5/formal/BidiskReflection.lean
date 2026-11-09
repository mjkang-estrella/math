import BidiskDegrees
namespace ContactPilot
noncomputable section
open MvPolynomial
set_option linter.unusedSimpArgs false

theorem reflect_add (p q : Poly₂) (m k : ℕ) (z w : ℂ) :
    reflect (p+q) m k z w = reflect p m k z w + reflect q m k z w := by
  classical
  change (p+q).coeff.sum (fun d c => star c * z^(m-d 0) * w^(k-d 1)) =
    p.coeff.sum (fun d c => star c * z^(m-d 0) * w^(k-d 1)) +
    q.coeff.sum (fun d c => star c * z^(m-d 0) * w^(k-d 1))
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index'
  · intro d; simp
  · intro d a b; simp [add_mul]

theorem reflect_monomial (d : Fin 2 →₀ ℕ) (c : ℂ) (m k : ℕ) (z w : ℂ) :
    reflect (monomial d c) m k z w = star c * z^(m-d 0) * w^(k-d 1) := by
  classical
  change (monomial d c).coeff.sum (fun d c => star c * z^(m-d 0) * w^(k-d 1)) = _
  apply MvPolynomial.sum_monomial_eq
  simp

private def bm (i j : ℕ) (c : ℂ) : Poly₂ :=
  monomial (Finsupp.single 0 i + Finsupp.single 1 j) c
private theorem bm_formula (i j : ℕ) (c : ℂ) : bm i j c = MvPolynomial.C c * Z^i * W^j := by
  rw [bm, monomial_add_single, ← C_mul_X_pow_eq_monomial]

private theorem denominator_expanded : bidiskDenominator =
    bm 3 2 (-2 + (6)*Complex.I) +
    bm 3 1 (0 + (2)*Complex.I) +
    bm 3 0 (2 + (0)*Complex.I) +
    bm 2 2 (-2 + (-6)*Complex.I) +
    bm 2 1 (0 + (6)*Complex.I) +
    bm 2 0 (2 + (0)*Complex.I) +
    bm 1 2 (2 + (-6)*Complex.I) +
    bm 1 1 (0 + (-10)*Complex.I) +
    bm 1 0 (-2 + (-8)*Complex.I) +
    bm 0 2 (2 + (-2)*Complex.I) +
    bm 0 1 (0 + (2)*Complex.I) +
    bm 0 0 (-2 + (-16)*Complex.I) := by
  unfold bidiskDenominator cayleyQ cayleyN
  simp only [bm_formula, map_add, map_mul, map_ofNat, map_neg]
  have hi : (MvPolynomial.C Complex.I : Poly₂)^2 = -1 := by rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hi3 : (MvPolynomial.C Complex.I : Poly₂)^3 = -MvPolynomial.C Complex.I := by
    linear_combination MvPolynomial.C Complex.I * hi
  have hi5 : (MvPolynomial.C Complex.I : Poly₂)^5 = MvPolynomial.C Complex.I := by
    calc
      _ = (MvPolynomial.C Complex.I)^2 * (MvPolynomial.C Complex.I)^2 * MvPolynomial.C Complex.I := by ring
      _ = _ := by rw [hi]; ring
  ring_nf
  simp only [hi, hi3, hi5, map_zero]
  ring

private theorem numerator_expanded : bidiskNumerator =
    bm 3 2 (-2 + (16)*Complex.I) +
    bm 3 1 (0 + (-2)*Complex.I) +
    bm 3 0 (2 + (2)*Complex.I) +
    bm 2 2 (-2 + (8)*Complex.I) +
    bm 2 1 (0 + (10)*Complex.I) +
    bm 2 0 (2 + (6)*Complex.I) +
    bm 1 2 (2 + (0)*Complex.I) +
    bm 1 1 (0 + (-6)*Complex.I) +
    bm 1 0 (-2 + (6)*Complex.I) +
    bm 0 2 (2 + (0)*Complex.I) +
    bm 0 1 (0 + (-2)*Complex.I) +
    bm 0 0 (-2 + (-6)*Complex.I) := by
  unfold bidiskNumerator cayleyQ cayleyN
  simp only [bm_formula, map_add, map_mul, map_ofNat, map_neg]
  have hi : (MvPolynomial.C Complex.I : Poly₂)^2 = -1 := by rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hi3 : (MvPolynomial.C Complex.I : Poly₂)^3 = -MvPolynomial.C Complex.I := by
    linear_combination MvPolynomial.C Complex.I * hi
  have hi5 : (MvPolynomial.C Complex.I : Poly₂)^5 = MvPolynomial.C Complex.I := by
    calc
      _ = (MvPolynomial.C Complex.I)^2 * (MvPolynomial.C Complex.I)^2 * MvPolynomial.C Complex.I := by ring
      _ = _ := by rw [hi]; ring
  ring_nf
  simp only [hi, hi3, hi5, map_zero]
  ring

private theorem reflect_bm (i j : ℕ) (c : ℂ) (z w : ℂ) :
    reflect (bm i j c) 3 2 z w = star c * z^(3-i) * w^(2-j) := by
  simp [bm, reflect_monomial, Finsupp.single_apply]

theorem bidisk_reflection (z w : ℂ) :
    eval₂ bidiskNumerator z w = (1:ℂ) * reflect bidiskDenominator 3 2 z w := by
  rw [denominator_expanded, numerator_expanded]
  simp only [reflect_add, reflect_bm]
  simp only [bm_formula]
  simp [eval₂, MvPolynomial.eval_monomial, Finsupp.prod_add_index,
    Finsupp.prod_single_index, Finsupp.single_apply, Z, W, Complex.I_sq]
  ring
end
end ContactPilot
