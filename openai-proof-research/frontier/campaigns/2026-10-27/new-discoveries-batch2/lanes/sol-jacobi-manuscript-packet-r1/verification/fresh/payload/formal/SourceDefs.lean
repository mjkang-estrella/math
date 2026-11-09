import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace JacobiShifted

abbrev QPoly := MvPolynomial (Fin 2) ℚ
abbrev GPoly := QuadraticAlgebra QPoly (-1) 0

/-- Polynomial Gaussian rationals: the generator has square -1. -/
def embed (p : QPoly) : GPoly := ⟨p, 0⟩
def scalar (q : ℚ) : GPoly := embed (MvPolynomial.C q)

def midpointX : GPoly := ⟨MvPolynomial.C (1 / 2), MvPolynomial.C (1 / 2)⟩
def midpointY : GPoly := ⟨MvPolynomial.C (1 / 2), MvPolynomial.C (-1 / 2)⟩

/-- The source Hankel numerator in the shifted parameter. -/
def hankelNumerator (i : Fin 2) (l : ℕ) : QPoly :=
  ∏ j ∈ Finset.range l,
    (MvPolynomial.X i - MvPolynomial.C ((j : ℚ) * (j + 1)))

/-- Literal inverse-factorial numerator C_s, evaluated at the source midpoint. -/
def sourceC (s : ℕ) : GPoly :=
  ∑ l ∈ Finset.range (s + 1),
    scalar (1 / ((l.factorial : ℚ) * ((s - l).factorial : ℚ))) *
      embed (hankelNumerator 0 l * hankelNumerator 1 (s - l)) *
      midpointX ^ l * midpointY ^ (s - l)

/-- Coefficients of prod_{j=1}^s (Z-j)^(-1), using the geometric series
of each factor. No Stirling-number identification is assumed. -/
def inverseFactorCoeff : ℕ → ℕ → ℚ
  | 0, n => if n = 0 then 1 else 0
  | s + 1, n => ∑ k ∈ Finset.range (n + 1),
      if k = 0 then 0 else ((s + 1 : ℕ) : ℚ) ^ (k - 1) *
        inverseFactorCoeff s (n - k)

/-- Coefficient of Z^(-n) in source equation (6). -/
def sourceFCoeff (n : ℕ) : GPoly :=
  ∑ s ∈ Finset.range (n + 1), scalar (inverseFactorCoeff s n) * sourceC s

def sourceAugmentCoeff (n : ℕ) : GPoly := if n = 0 then 0 else sourceFCoeff n

/-- Finite convolution: coefficient n of the kth power of a formal series. -/
def powerCoeff (f : ℕ → GPoly) : ℕ → ℕ → GPoly
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => ∑ j ∈ Finset.range (n + 1), f j * powerCoeff f k (n - j)

/-- Literal formal logarithm sum. The augmentation has zero constant term. -/
def sourceLogCoeff (n : ℕ) : GPoly :=
  ∑ k ∈ Finset.range (n + 1),
    if k = 0 then 0 else
      scalar (((-1 : ℚ) ^ (k + 1)) / (k : ℚ)) * powerCoeff sourceAugmentCoeff k n

/-- Definition 2.1 (7), in independent shifted variables u and v.
Order zero is a harmless convention outside the source domain. -/
def sourceKappa (r : ℕ) : QPoly :=
  if r = 0 then 0 else
    MvPolynomial.C (((2 : ℚ) ^ (2 * r - 1))⁻¹) * (sourceLogCoeff (2 * r - 1)).im

def TwoLocal (q : ℚ) : Prop := Odd q.den

def dyadicExponent (r : ℕ) : ℕ := 2 * r + padicValNat 2 ((r - 1).factorial)

/-- Exact dyadic denominator, with the pure-u coefficient witnessing sharpness.
This definition does not assert that the claim has been proved. -/
def SourceClaim : Prop := ∀ r : ℕ, 1 ≤ r →
  (∀ m : Fin 2 →₀ ℕ,
    TwoLocal ((2 : ℚ) ^ dyadicExponent r * (sourceKappa r).coeff m)) ∧
  ¬ TwoLocal ((2 : ℚ) ^ (dyadicExponent r - 1) *
    (sourceKappa r).coeff (Finsupp.single 0 r))

theorem sourceKappa_zero : sourceKappa 0 = 0 := by
  simp [sourceKappa]

theorem inverseFactorCoeff_zero (n : ℕ) :
    inverseFactorCoeff 0 n = if n = 0 then 1 else 0 := rfl

end JacobiShifted
