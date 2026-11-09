import LiteralHankel

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.SourceBridge

theorem imaginaryUnit_mul_injective : Function.Injective (fun z : G => imaginaryUnit*z) := by
  intro a b h
  have h' := congrArg (fun z : G => imaginaryUnit*z) h
  simpa only [imaginaryUnit_twice, neg_inj] using h'

theorem xi_product : xi*(xi-1)=
    gaussianEmbed (-rationalScalar (1/2)*MvPolynomial.C MidpointRational.w*MvPolynomial.C t) := by
  apply imaginaryUnit_mul_injective
  dsimp only
  rw [← mul_assoc imaginaryUnit xi, ← deltaG_xi]
  apply QuadraticAlgebra.ext <;>
    simp [xi, imaginaryUnit, deltaA_mul, delta_t, gaussianEmbed] <;> ring

theorem eta_product : eta*(eta-1)=
    gaussianEmbed (-rationalScalar (1/2)*MvPolynomial.C MidpointRational.w*MvPolynomial.C tInv) := by
  apply imaginaryUnit_mul_injective
  dsimp only
  rw [← mul_assoc imaginaryUnit eta, ← deltaG_eta]
  apply QuadraticAlgebra.ext <;>
    simp [eta, imaginaryUnit, deltaA_mul, delta_tInv, gaussianEmbed] <;> ring

def S : A := rationalScalar (1/2)*
  ((MvPolynomial.X 0+MvPolynomial.X 1)*MvPolynomial.C (MidpointRational.w^2)+
    (MvPolynomial.X 0-MvPolynomial.X 1)*MvPolynomial.C (MidpointRational.w*MidpointRational.x))

theorem potentialCurve_eq : potentialCurve=gaussianEmbed S := by
  dsimp [potentialCurve]
  rw [mul_assoc (parameter 0) xi, xi_product, mul_assoc (parameter 1) eta, eta_product]
  apply QuadraticAlgebra.ext <;>
    simp [parameter, coeffEmbed, paramEmbed, gaussianEmbed, S, t, tInv, pow_two] <;> ring

/-- R1 with the explicit rational midpoint potential from the integral sequence. -/
theorem literal_hankel_midpoint_R1 (s : ℕ) :
    deltaG (deltaG (C s))+imaginaryUnit*(s : G)*deltaG (C s)+
      imaginaryUnit*deltaG (C (s+1))-gaussianEmbed S*C s=0 := by
  rw [← potentialCurve_eq]
  exact literal_hankel_R1 s

end JacobiShifted.SourceBridge
