import SourceClaim
set_option autoImplicit false
set_option warningAsError true
#check fun (r : ℕ) (hr : 1 ≤ r) => JacobiShifted.source_claim r hr
#check fun (r : ℕ) (hr : 1 ≤ r) =>
  (show (∀ m : Fin 2 →₀ ℕ,
    Odd (((2 : ℚ)^(2*r + padicValNat 2 ((r-1).factorial)) *
      ((if r=0 then 0 else MvPolynomial.C (((2 : ℚ)^(2*r-1))⁻¹) *
        (JacobiShifted.sourceLogCoeff (2*r-1)).im) : JacobiShifted.QPoly).coeff m)).den) ∧
    ¬ Odd (((2 : ℚ)^((2*r + padicValNat 2 ((r-1).factorial))-1) *
      ((if r=0 then 0 else MvPolynomial.C (((2 : ℚ)^(2*r-1))⁻¹) *
        (JacobiShifted.sourceLogCoeff (2*r-1)).im) : JacobiShifted.QPoly).coeff (Finsupp.single 0 r))).den
   from by simpa only [JacobiShifted.TwoLocal, JacobiShifted.dyadicExponent,
     JacobiShifted.sourceKappa] using JacobiShifted.source_claim r hr)
#print JacobiShifted.sourceLogCoeff
#print JacobiShifted.sourceAugmentCoeff
#print JacobiShifted.sourceFCoeff
#print JacobiShifted.sourceC
#print JacobiShifted.hankelNumerator
#print JacobiShifted.inverseFactorCoeff
#print JacobiShifted.powerCoeff
#print JacobiShifted.midpointX
#print JacobiShifted.midpointY
