import LiteralFinite
import MidpointRational

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.SourceBridge

abbrev A := MvPolynomial (Fin 2) MidpointRational.QAlg
abbrev G := QuadraticAlgebra A (-1) 0

/-- This map changes the coefficient ring and retains the Gaussian generator. -/
def gaussianMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    QuadraticAlgebra R (-1) 0 →+* QuadraticAlgebra S (-1) 0 where
  toFun z := ⟨f z.re, f z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_one' := by apply QuadraticAlgebra.ext <;>
    simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' a b := by apply QuadraticAlgebra.ext <;> simp [map_add]
  map_mul' a b := by apply QuadraticAlgebra.ext <;> simp [map_add, map_mul]

@[simp] theorem gaussianMap_re {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : QuadraticAlgebra R (-1) 0) :
    (gaussianMap f z).re = f z.re := rfl
@[simp] theorem gaussianMap_im {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : QuadraticAlgebra R (-1) 0) :
    (gaussianMap f z).im = f z.im := rfl

def gaussianEmbed {R : Type*} [CommRing R] : R →+* QuadraticAlgebra R (-1) 0 :=
  algebraMap R _

def rationalBase : ℚ →+* MidpointRational.QAlg := MidpointRational.C.comp Polynomial.C
def paramEmbed : QPoly →+* A := MvPolynomial.map rationalBase
def coeffEmbed : QPoly →+* G := gaussianEmbed.comp paramEmbed
def rationalScalar (q : ℚ) : A := paramEmbed (MvPolynomial.C q)

def t : MidpointRational.QAlg := MidpointRational.w + MidpointRational.x
def tInv : MidpointRational.QAlg := MidpointRational.w - MidpointRational.x

theorem t_mul_tInv : t*tInv=1 := by
  dsimp [t, tInv]
  calc
    (MidpointRational.w + MidpointRational.x)*(MidpointRational.w-MidpointRational.x) = MidpointRational.w^2-MidpointRational.x^2 := by ring
    _ = 1 := by rw [MidpointRational.w_sq]; ring

/-- Gaussian coordinates; their `.im` is over `A`, not the `w` coordinate. -/
def xi : G := ⟨rationalScalar (1/2), rationalScalar (1/2)*MvPolynomial.C t⟩
def eta : G := ⟨rationalScalar (1/2), -rationalScalar (1/2)*MvPolynomial.C tInv⟩

def midpointA : A →+* QPoly := MvPolynomial.map MidpointRational.midpoint
def midpointG : G →+* GPoly := gaussianMap midpointA
def tauA : A →+* A := MvPolynomial.map MidpointRational.tau
def tauG : G →+* G := gaussianMap tauA

def conjugate : G →+* G where
  toFun z := ⟨z.re,-z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_one' := by apply QuadraticAlgebra.ext <;>
    simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' a b := by apply QuadraticAlgebra.ext <;> simp <;> ring
  map_mul' a b := by apply QuadraticAlgebra.ext <;> simp <;> ring

@[simp] theorem conjugate_re (z : G) : (conjugate z).re=z.re := rfl
@[simp] theorem conjugate_im (z : G) : (conjugate z).im= -z.im := rfl

@[simp] theorem midpoint_rationalBase (q : ℚ) : MidpointRational.midpoint (rationalBase q)=q := by
  simp [rationalBase]

@[simp] theorem tau_rationalBase (q : ℚ) : MidpointRational.tau (rationalBase q)=rationalBase q := by
  apply QuadraticAlgebra.ext <;> simp [rationalBase, MidpointRational.C, MidpointRational.tau, MidpointRational.flip_apply]

@[simp] theorem midpoint_paramEmbed (p : QPoly) : midpointA (paramEmbed p)=p := by
  change MvPolynomial.map MidpointRational.midpoint (MvPolynomial.map rationalBase p)=p
  rw [MvPolynomial.map_map]
  have he : MidpointRational.midpoint.comp rationalBase=RingHom.id ℚ :=
    RingHom.ext midpoint_rationalBase
  rw [he, MvPolynomial.map_id]

@[simp] theorem tau_paramEmbed (p : QPoly) : tauA (paramEmbed p)=paramEmbed p := by
  change MvPolynomial.map MidpointRational.tau (MvPolynomial.map rationalBase p)=_
  rw [MvPolynomial.map_map]
  have he : MidpointRational.tau.comp rationalBase=rationalBase :=
    RingHom.ext tau_rationalBase
  rw [he]
  rfl

@[simp] theorem midpoint_coeffEmbed (p : QPoly) : midpointG (coeffEmbed p)=sourceEmbed p := by
  apply QuadraticAlgebra.ext <;>
    simp [midpointG, coeffEmbed, gaussianEmbed, sourceEmbed, embed]

@[simp] theorem tau_coeffEmbed (p : QPoly) : tauG (coeffEmbed p)=conjugate (coeffEmbed p) := by
  apply QuadraticAlgebra.ext <;> simp [tauG, coeffEmbed, gaussianEmbed]

@[simp] theorem midpoint_xi : midpointG xi=midpointX := by
  apply QuadraticAlgebra.ext <;>
    simp [midpointG, xi, rationalScalar, midpointA, paramEmbed, t, midpointX, rationalBase, MidpointRational.C]

@[simp] theorem midpoint_eta : midpointG eta=midpointY := by
  apply QuadraticAlgebra.ext <;>
    simp [midpointG, eta, rationalScalar, midpointA, paramEmbed, tInv, midpointY, rationalBase, MidpointRational.C, neg_div]

@[simp] theorem tau_xi : tauG xi=conjugate xi := by
  apply QuadraticAlgebra.ext <;>
    simp [tauG, xi, rationalScalar, tauA, paramEmbed, t, map_neg] <;> ring

@[simp] theorem tau_eta : tauG eta=conjugate eta := by
  apply QuadraticAlgebra.ext <;>
    simp [tauG, eta, rationalScalar, tauA, paramEmbed, tInv, map_sub] <;> ring

def C (s : ℕ) : G := literalC coeffEmbed xi eta s
def F (n : ℕ) : G := literalF coeffEmbed xi eta n
def L (n : ℕ) : G := literalLog coeffEmbed xi eta n

theorem midpoint_C (s : ℕ) : midpointG (C s)=sourceC s := by
  rw [C, map_literalC, midpoint_xi, midpoint_eta]
  have he : midpointG.comp coeffEmbed=sourceEmbed := RingHom.ext midpoint_coeffEmbed
  rw [he, literalC_source]

theorem midpoint_F (n : ℕ) : midpointG (F n)=sourceFCoeff n := by
  rw [F, map_literalF, midpoint_xi, midpoint_eta]
  have he : midpointG.comp coeffEmbed=sourceEmbed := RingHom.ext midpoint_coeffEmbed
  rw [he, literalF_source]

theorem midpoint_L (n : ℕ) : midpointG (L n)=sourceLogCoeff n := by
  rw [L, map_literalLog, midpoint_xi, midpoint_eta]
  have he : midpointG.comp coeffEmbed=sourceEmbed := RingHom.ext midpoint_coeffEmbed
  rw [he, literalLog_source]

theorem tau_C (s : ℕ) : tauG (C s)=conjugate (C s) := by
  rw [C, map_literalC, map_literalC, tau_xi, tau_eta]
  have he : tauG.comp coeffEmbed=conjugate.comp coeffEmbed := RingHom.ext tau_coeffEmbed
  rw [he]

theorem tau_F (n : ℕ) : tauG (F n)=conjugate (F n) := by
  rw [F, map_literalF, map_literalF, tau_xi, tau_eta]
  have he : tauG.comp coeffEmbed=conjugate.comp coeffEmbed := RingHom.ext tau_coeffEmbed
  rw [he]

theorem tau_L (n : ℕ) : tauG (L n)=conjugate (L n) := by
  rw [L, map_literalLog, map_literalLog, tau_xi, tau_eta]
  have he : tauG.comp coeffEmbed=conjugate.comp coeffEmbed := RingHom.ext tau_coeffEmbed
  rw [he]

/-- Closed normalization for the literal finite logarithm, at every order. -/
theorem literal_imaginary_normalization (n : ℕ) :
    tauA (L n).im= -(L n).im ∧ midpointA (L n).im=(sourceLogCoeff n).im := by
  constructor
  · exact congrArg QuadraticAlgebra.im (tau_L n)
  · exact congrArg QuadraticAlgebra.im (midpoint_L n)

end JacobiShifted.SourceBridge
