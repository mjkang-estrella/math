import RealAnalytic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MittagModulus

theorem sourceExpression_eq_normSq {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    sourceExpression a t =
      Complex.normSq (mittagLeffler a 1 ((Real.sqrt t : ℂ) * Complex.I)) := by
  have hs : (Real.sqrt t : ℂ) ^ 2 = (t : ℂ) := by
    exact_mod_cast Real.sq_sqrt ht
  have hz : ((Real.sqrt t : ℂ) * Complex.I) ^ 2 = -(t : ℂ) := by
    rw [mul_pow, Complex.I_sq, hs]
    ring
  have he := mittagLeffler_even_odd ha zero_lt_one
    ((Real.sqrt t : ℂ) * Complex.I)
  rw [hz] at he
  have hA : mittagLeffler (2 * a) 1 (-(t : ℂ)) = (mittagReal (2 * a) 1 (-t) : ℂ) := by
    simpa only [Complex.ofReal_neg] using mittagLeffler_ofReal (2 * a) 1 (-t)
  have hB : mittagLeffler (2 * a) (a + 1) (-(t : ℂ)) =
      (mittagReal (2 * a) (1 + a) (-t) : ℂ) := by
    simpa only [add_comm a 1, Complex.ofReal_neg] using mittagLeffler_ofReal (2 * a) (a + 1) (-t)
  rw [he, hA, hB, sourceExpression_real]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, zero_add, add_zero, sub_zero, mul_one]
  nlinarith [Real.sq_sqrt ht]

end MittagModulus
