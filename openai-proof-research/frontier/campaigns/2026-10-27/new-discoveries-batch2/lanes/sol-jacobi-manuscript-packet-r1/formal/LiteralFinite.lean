import SourceDefs
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
set_option warningAsError true

noncomputable section
namespace JacobiShifted.SourceBridge

/-- The literal source formulas, with only their evaluation ring generalized. -/
def literalC {R : Type*} [CommRing R] (e : QPoly →+* R) (ξ η : R) (s : ℕ) : R :=
  ∑ l ∈ Finset.range (s + 1),
    e (MvPolynomial.C (1 / ((l.factorial : ℚ) * ((s-l).factorial : ℚ)))) *
      e (hankelNumerator 0 l * hankelNumerator 1 (s-l)) * ξ^l * η^(s-l)

def literalF {R : Type*} [CommRing R] (e : QPoly →+* R) (ξ η : R) (n : ℕ) : R :=
  ∑ s ∈ Finset.range (n+1), e (MvPolynomial.C (inverseFactorCoeff s n)) *
    literalC e ξ η s

def augment {R : Type*} [Zero R] (f : ℕ → R) (n : ℕ) : R :=
  if n=0 then 0 else f n

def finitePower {R : Type*} [CommRing R] (f : ℕ → R) : ℕ → ℕ → R
  | 0, n => if n=0 then 1 else 0
  | k+1, n => ∑ j ∈ Finset.range (n+1), f j * finitePower f k (n-j)

def literalLog {R : Type*} [CommRing R] (e : QPoly →+* R) (ξ η : R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n+1), if k=0 then 0 else
    e (MvPolynomial.C (((-1 : ℚ)^(k+1))/(k : ℚ))) *
      finitePower (augment (literalF e ξ η)) k n

theorem map_literalC {R S : Type*} [CommRing R] [CommRing S]
    (h : R →+* S) (e : QPoly →+* R) (ξ η : R) (s : ℕ) :
    h (literalC e ξ η s) = literalC (h.comp e) (h ξ) (h η) s := by
  simp [literalC, map_sum, map_mul, map_pow]

theorem map_literalF {R S : Type*} [CommRing R] [CommRing S]
    (h : R →+* S) (e : QPoly →+* R) (ξ η : R) (n : ℕ) :
    h (literalF e ξ η n) = literalF (h.comp e) (h ξ) (h η) n := by
  simp [literalF, map_sum, map_mul, map_literalC]

theorem map_augment {R S : Type*} [CommRing R] [CommRing S]
    (h : R →+* S) (f : ℕ → R) (n : ℕ) :
    h (augment f n) = augment (fun j => h (f j)) n := by
  by_cases hn : n=0 <;> simp [augment, hn]

theorem map_finitePower {R S : Type*} [CommRing R] [CommRing S]
    (h : R →+* S) (f : ℕ → R) (k n : ℕ) :
    h (finitePower f k n) = finitePower (fun j => h (f j)) k n := by
  induction k generalizing n with
  | zero => by_cases hn : n=0 <;> simp [finitePower, hn]
  | succ k ih => simp [finitePower, map_sum, map_mul, ih]

theorem map_literalLog {R S : Type*} [CommRing R] [CommRing S]
    (h : R →+* S) (e : QPoly →+* R) (ξ η : R) (n : ℕ) :
    h (literalLog e ξ η n) = literalLog (h.comp e) (h ξ) (h η) n := by
  simp only [literalLog, map_sum, apply_ite, map_zero, map_mul, map_finitePower]
  simp only [map_augment, map_literalF, RingHom.comp_apply]

def sourceEmbed : QPoly →+* GPoly where
  toFun := embed
  map_zero' := by apply QuadraticAlgebra.ext <;> simp [embed]
  map_one' := by apply QuadraticAlgebra.ext <;> simp [embed, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' a b := by apply QuadraticAlgebra.ext <;> simp [embed]
  map_mul' a b := by apply QuadraticAlgebra.ext <;> simp [embed]

theorem literalC_source (s : ℕ) :
    literalC sourceEmbed midpointX midpointY s = sourceC s := rfl

theorem literalF_source (n : ℕ) :
    literalF sourceEmbed midpointX midpointY n = sourceFCoeff n := rfl

theorem finitePower_source (f : ℕ → GPoly) (k n : ℕ) :
    finitePower f k n = powerCoeff f k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [finitePower, powerCoeff, ih]

theorem literalLog_source (n : ℕ) :
    literalLog sourceEmbed midpointX midpointY n = sourceLogCoeff n := by
  simp only [literalLog, sourceLogCoeff, finitePower_source]
  rfl

end JacobiShifted.SourceBridge
