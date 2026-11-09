import SourceDefs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open JacobiShifted

theorem sourceKappa_one : sourceKappa 1 =
    MvPolynomial.C (1 / 4 : ℚ) * (MvPolynomial.X 0 - MvPolynomial.X 1) := by
  norm_num [sourceKappa, sourceLogCoeff, powerCoeff, sourceAugmentCoeff,
    sourceFCoeff, inverseFactorCoeff, sourceC, hankelNumerator,
    scalar, embed, midpointX, midpointY, QuadraticAlgebra.mk_mul_mk,
    Finset.sum_range_succ]
  have h : (MvPolynomial.C (1 / 2 : ℚ) : QPoly) ^ 2 = MvPolynomial.C (1 / 4 : ℚ) := by
    rw [← map_pow]
    norm_num
  calc
    _ = (MvPolynomial.C (1 / 2 : ℚ) : QPoly) ^ 2 *
        (MvPolynomial.X 0 - MvPolynomial.X 1) := by ring
    _ = _ := by rw [h]

#check SourceClaim
#check sourceKappa
#print axioms sourceKappa_zero
#print axioms inverseFactorCoeff_zero
#print axioms sourceKappa_one
