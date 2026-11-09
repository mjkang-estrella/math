import SourceClaim

set_option autoImplicit false
set_option warningAsError true

#check JacobiShifted.source_claim
#print axioms JacobiShifted.source_claim
#print JacobiShifted.SourceClaim
#print JacobiShifted.sourceKappa
#print JacobiShifted.dyadicExponent
#print JacobiShifted.TwoLocal
#check JacobiShifted.SourceBridge.sourceKappa_twoLocal
#check JacobiShifted.SourceBridge.sourceKappa_pure_u_valuation
#check JacobiShifted.SourceBridge.sourceKappa_pure_u_sharp
#check (JacobiShifted.source_claim : ∀ r : ℕ, 1 ≤ r →
  (∀ m : Fin 2 →₀ ℕ,
    JacobiShifted.TwoLocal ((2 : ℚ)^JacobiShifted.dyadicExponent r *
      (JacobiShifted.sourceKappa r).coeff m)) ∧
  ¬ JacobiShifted.TwoLocal ((2 : ℚ)^(JacobiShifted.dyadicExponent r - 1) *
    (JacobiShifted.sourceKappa r).coeff (Finsupp.single 0 r)))
