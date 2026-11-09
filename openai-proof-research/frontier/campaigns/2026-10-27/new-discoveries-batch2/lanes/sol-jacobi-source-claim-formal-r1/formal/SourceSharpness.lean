import LiteralPureCoefficient
import DyadicArithmetic

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace JacobiShifted.SourceBridge
open BinaryFiltration DyadicArithmetic
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem sourceKappa_pure_u_ne_zero (r : ℕ) (hr : 1 ≤ r) :
    (sourceKappa r).coeff (Finsupp.single 0 r) ≠ 0 := by
  rw [sourceKappa_pure_u r hr]
  exact div_ne_zero (mul_ne_zero (by exact_mod_cast catalan_ne_zero (r-1))
    (binomialOddSum_ne_zero (r-1))) (pow_ne_zero _ (by norm_num))

theorem sourceKappa_pure_u_valuation (r : ℕ) (hr : 1 ≤ r) :
    padicValRat 2 ((sourceKappa r).coeff (Finsupp.single 0 r)) =
      -(dyadicExponent r : ℤ) := by
  rw [sourceKappa_pure_u r hr,
    padicValRat.div
      (mul_ne_zero (by exact_mod_cast catalan_ne_zero (r-1)) (binomialOddSum_ne_zero (r-1)))
      (pow_ne_zero _ (by norm_num)),
    padicValRat.mul (by exact_mod_cast catalan_ne_zero (r-1)) (binomialOddSum_ne_zero (r-1)),
    catalan_valuation, binomialOddSum_valuation, padicValRat.pow]
  have htwo : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (by norm_num : 1 < (2 : ℕ))
  rw [htwo, mul_one]
  have hf := factorial_valuation (r-1)
  unfold dyadicExponent
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

theorem sourceKappa_pure_u_sharp (r : ℕ) (hr : 1 ≤ r) :
    ¬ JacobiShifted.TwoLocal ((2 : ℚ)^(dyadicExponent r - 1) *
      (sourceKappa r).coeff (Finsupp.single 0 r)) := by
  rw [twoLocal_iff_valuation_nonneg,
    padicValRat.mul (pow_ne_zero _ (by norm_num)) (sourceKappa_pure_u_ne_zero r hr),
    padicValRat.pow, sourceKappa_pure_u_valuation r hr]
  have htwo : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (by norm_num : 1 < (2 : ℕ))
  rw [htwo, mul_one]
  have hE : 1 ≤ dyadicExponent r := by unfold dyadicExponent; omega
  omega

end JacobiShifted.SourceBridge
