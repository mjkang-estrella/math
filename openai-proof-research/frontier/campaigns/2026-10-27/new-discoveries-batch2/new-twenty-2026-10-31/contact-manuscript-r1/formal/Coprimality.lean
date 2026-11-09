import SourceContact
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.UniqueFactorization

set_option linter.unusedSimpArgs false

namespace ContactPilot
noncomputable section
open MvPolynomial
abbrev Z : Poly₂ := X 0
abbrev W : Poly₂ := X 1
def factorMinus : Poly₂ := W * Z - W - 1
def factorPlus : Poly₂ := W * Z + W - 1
def n : Poly₂ := factorMinus * factorPlus
def q : Poly₂ := -W^2 * Z^3 + 2*W^2*Z + 4*W*Z^2 + 2*W*Z - W - 3*Z

private theorem inner_coprime_minus :
    IsCoprime (X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ) (-X 0 - 1) := by
  refine ⟨-1, -1, ?_⟩
  ring
private theorem inner_coprime_plus :
    IsCoprime (X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ) (X 0 - 1) := by
  refine ⟨1, -1, ?_⟩
  ring

theorem factorMinus_irreducible : Irreducible factorMinus := by
  apply (MulEquiv.irreducible_iff (f := (MvPolynomial.finSuccEquiv ℂ 1))).mp
  have h := Polynomial.irreducible_C_mul_X_add_C
    (MvPolynomial.X_ne_zero (0 : Fin 1) : (X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ) ≠ 0)
    inner_coprime_minus.isRelPrime
  convert h using 1; simp only [factorMinus, Z, W, map_sub, map_mul,
    map_one, map_neg, Polynomial.C_sub, Polynomial.C_neg, Polynomial.C_1,
    MvPolynomial.finSuccEquiv_X_zero, show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    MvPolynomial.finSuccEquiv_X_succ] ; ring

theorem factorPlus_irreducible : Irreducible factorPlus := by
  apply (MulEquiv.irreducible_iff (f := (MvPolynomial.finSuccEquiv ℂ 1))).mp
  have h := Polynomial.irreducible_C_mul_X_add_C
    (MvPolynomial.X_ne_zero (0 : Fin 1) : (X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ) ≠ 0)
    inner_coprime_plus.isRelPrime
  convert h using 1; simp only [factorPlus, Z, W, map_sub, map_mul, map_add,
    map_one, map_neg, Polynomial.C_sub, Polynomial.C_neg, Polynomial.C_1,
    MvPolynomial.finSuccEquiv_X_zero, show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    MvPolynomial.finSuccEquiv_X_succ] ; ring

theorem factorMinus_not_dvd_q : ¬ factorMinus ∣ q := by
  rintro ⟨s, hs⟩
  have h := congrArg (MvPolynomial.eval (fun j : Fin 2 => if j = 0 then (0 : ℂ) else -1)) hs
  norm_num [q, factorMinus, Z, W] at h

theorem factorPlus_not_dvd_q : ¬ factorPlus ∣ q := by
  rintro ⟨s, hs⟩
  have h := congrArg (MvPolynomial.eval (fun j : Fin 2 => if j = 0 then (0 : ℂ) else 1)) hs
  norm_num [q, factorPlus, Z, W] at h

-- This is the requested common-divisor statement in the original ring.
theorem numerator_denominator_reduced : ∀ d : Poly₂, d ∣ n → d ∣ q → IsUnit d := by
  have h₁ := factorMinus_irreducible.isRelPrime_iff_not_dvd.mpr factorMinus_not_dvd_q
  have h₂ := factorPlus_irreducible.isRelPrime_iff_not_dvd.mpr factorPlus_not_dvd_q
  exact h₁.mul_left h₂
end
end ContactPilot
