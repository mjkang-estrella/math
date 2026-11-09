import LiteralPotential
import LiteralInverseFactor

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.SourceBridge

def subVar (i : Fin 2) : A := if i=0 then
  rationalScalar (1/2)*(MvPolynomial.X 0+MvPolynomial.X 1) else
  rationalScalar (1/2)*(MvPolynomial.X 0-MvPolynomial.X 1)

/-- An identity substitution only: no divisibility-preservation claim is made. -/
def scale : Midpoint.Param →+* A :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MidpointRational.lift) subVar

def integralOp : Midpoint.Param →+ Midpoint.Param :=
  BinaryFiltration.coefficientOperator Midpoint.delta

@[simp] theorem integralOp_C (z : Midpoint.R) :
    integralOp (MvPolynomial.C z)=MvPolynomial.C (Midpoint.delta z) := by
  apply MvPolynomial.ext
  intro m
  simp only [integralOp, BinaryFiltration.coefficientOperator_coeff, MvPolynomial.coeff_C]
  split_ifs <;> simp

theorem integralOp_mul_X (p : Midpoint.Param) (i : Fin 2) :
    integralOp (p*MvPolynomial.X i)=integralOp p*MvPolynomial.X i := by
  apply MvPolynomial.ext
  intro m
  simp only [integralOp, BinaryFiltration.coefficientOperator_coeff, MvPolynomial.coeff_mul_X']
  split_ifs <;> simp

@[simp] theorem deltaA_X (i : Fin 2) : deltaA (MvPolynomial.X i)=0 := by
  have h := deltaA_paramEmbed (MvPolynomial.X i)
  simpa only [paramEmbed, MvPolynomial.map_X] using h

@[simp] theorem deltaA_subVar (i : Fin 2) : deltaA (subVar i)=0 := by
  by_cases hi : i=0 <;> simp [subVar, hi, deltaA_mul]

@[simp] theorem scale_C (z : Midpoint.R) :
    scale (MvPolynomial.C z)=MvPolynomial.C (MidpointRational.lift z) := by simp [scale]

@[simp] theorem scale_X (i : Fin 2) : scale (MvPolynomial.X i)=subVar i := by simp [scale]

theorem scale_delta (p : Midpoint.Param) : scale (integralOp p)=deltaA (scale p) := by
  induction p using MvPolynomial.induction_on with
  | C z => simp only [integralOp_C, scale_C, deltaA_C, MidpointRational.lift_delta]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [integralOp_mul_X, map_mul, map_mul, deltaA_mul, scale_X, deltaA_subVar, mul_zero,
      add_zero, hp]

def scaledH (n : ℕ) : A := scale (Midpoint.h n)

@[simp] theorem scaledH_zero : scaledH 0=0 := by simp [scaledH]

@[simp] theorem scaledH_one : scaledH 1=S := by
  simp [scaledH, Midpoint.P, BinaryFiltration.initial_eq_variables, subVar, S]
  ring

theorem scaledH_recurrence (n : ℕ) (hn : 1≤n) :
    scaledH (n+1)= -deltaA (scaledH n)-
      ∑ i ∈ Finset.range (n+1), scaledH i*scaledH (n-i) := by
  rw [scaledH, Midpoint.h_recurrence n hn]
  simp only [map_sub, map_neg, map_sum, map_mul]
  rw [show BinaryFiltration.coefficientOperator Midpoint.delta=integralOp from rfl, scale_delta]
  rfl

@[simp] theorem F_zero : F 0=1 := by simp [F_weighted, weight, inverseFactorCoeff]

@[simp] theorem L_one : L 1=F 1 := by
  norm_num [L, literalLog, finitePower, augment, Finset.sum_range_succ]
  rfl

theorem logarithmic_derivative_one : deltaG (L 1)= -imaginaryUnit*gaussianEmbed (scaledH 1) := by
  have h := literal_F_R2 0
  simp only [F_zero, deltaG_one, map_zero, zero_add, mul_one] at h
  apply imaginaryUnit_mul_injective
  dsimp only
  rw [L_one, scaledH_one]
  calc
    _ = potentialCurve := sub_eq_zero.mp h
    _ = imaginaryUnit*(-imaginaryUnit*gaussianEmbed S) := by
      rw [potentialCurve_eq]
      symm
      calc
        _ = -(imaginaryUnit*(imaginaryUnit*gaussianEmbed S)) := by ring
        _ = _ := by rw [imaginaryUnit_twice, neg_neg]

theorem imaginary_logarithmic_derivative_one : deltaA (L 1).im= -scaledH 1 := by
  calc
    _ = (-imaginaryUnit*gaussianEmbed (scaledH 1)).im :=
      congrArg QuadraticAlgebra.im logarithmic_derivative_one
    _ = _ := by simp [imaginaryUnit, gaussianEmbed] <;> ring

/-- The concrete all-order finite-source linear bridge, including normalization. -/
theorem literal_source_linear_bridge (n : ℕ) :
    midpointG (F n)=sourceFCoeff n ∧ midpointG (L n)=sourceLogCoeff n ∧
    deltaG (deltaG (F n))+imaginaryUnit*deltaG (F (n+1))-gaussianEmbed S*F n=0 ∧
    tauA (L n).im= -(L n).im ∧ midpointA (L n).im=(sourceLogCoeff n).im := by
  refine ⟨midpoint_F n, midpoint_L n, ?_, literal_imaginary_normalization n⟩
  rw [← potentialCurve_eq]
  exact literal_F_R2 n

end JacobiShifted.SourceBridge
