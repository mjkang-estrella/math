import MidpointNormalForm
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Span

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.MidpointRational
open Polynomial

abbrev QPoly := Polynomial ℚ
def q : QPoly := 1 + X ^ 2
abbrev QAlg := QuadraticAlgebra QPoly q 0

def C : QPoly →+* QAlg := algebraMap QPoly QAlg
def x : QAlg := ⟨X, 0⟩
def w : QAlg := ⟨0, 1⟩

@[simp] theorem C_re (p : QPoly) : (C p).re = p := rfl
@[simp] theorem C_im (p : QPoly) : (C p).im = 0 := rfl
@[simp] theorem x_re : x.re = X := rfl
@[simp] theorem x_im : x.im = 0 := rfl
@[simp] theorem w_re : w.re = 0 := rfl
@[simp] theorem w_im : w.im = 1 := rfl

theorem pair_mul (a b c d : QPoly) :
    (⟨a,b⟩ : QAlg) * ⟨c,d⟩ = ⟨a*c+q*b*d, a*d+b*c⟩ := by
  apply QuadraticAlgebra.ext <;> simp

theorem pair_eq_iff (a b c d : QPoly) :
    (⟨a,b⟩ : QAlg) = ⟨c,d⟩ ↔ a=c ∧ b=d := QuadraticAlgebra.ext_iff

theorem pair_normal (z : QAlg) : z = C z.re + w * C z.im := by
  apply QuadraticAlgebra.ext <;> simp [C, w]

theorem w_sq : w ^ 2 = 1 + x ^ 2 := by
  rw [pow_two, pow_two]
  apply QuadraticAlgebra.ext
  · rw [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul]
    simp [q, QuadraticAlgebra.re_one, pow_two]
  · rw [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul]
    simp [QuadraticAlgebra.im_one]

theorem w_mul_pair (a b : QPoly) : w * (⟨a,b⟩ : QAlg) = ⟨q*b,a⟩ := by
  apply QuadraticAlgebra.ext <;> simp [w]

/-- The rational midpoint differential operator on actual polynomial pairs. -/
def delta : QAlg →+ QAlg where
  toFun z := ⟨-q * derivative z.re, -X * z.im - q * derivative z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_add' a b := by apply QuadraticAlgebra.ext <;> simp [derivative_add] <;> ring

@[simp] theorem partial_re (z : QAlg) : (delta z).re = -q * derivative z.re := rfl
@[simp] theorem partial_im (z : QAlg) :
    (delta z).im = -X * z.im - q * derivative z.im := rfl

@[simp] theorem derivative_q : derivative q = 2 * X := by
  simp [q, derivative_add, derivative_pow, Polynomial.C_ofNat]

theorem partial_mul (a b : QAlg) : delta (a*b) = delta a*b + a*delta b := by
  apply QuadraticAlgebra.ext <;> simp [delta, derivative_add, derivative_mul, derivative_q] <;> ring

/-- The same concrete operator, bundled as a derivation over the integers. -/
def derivation : Derivation ℤ QAlg QAlg :=
  Derivation.mk' delta.toIntLinearMap (fun a b => by
    change delta (a*b) = a*delta b + b*delta a
    rw [partial_mul]
    ring)

@[simp] theorem derivation_apply (z : QAlg) : derivation z = delta z := rfl

@[simp] theorem partial_x : delta x = -(1 + x^2) := by
  rw [← w_sq, pow_two]
  apply QuadraticAlgebra.ext
  · rw [partial_re, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_mul]
    simp
  · rw [partial_im, QuadraticAlgebra.im_neg, QuadraticAlgebra.im_mul]
    simp

@[simp] theorem partial_w : delta w = -(w*x) := by
  apply QuadraticAlgebra.ext <;> simp [delta, w, x]

/-- Reflection in the quadratic generator, defined on both coordinates. -/
def rho : QAlg →+* QAlg where
  toFun z := ⟨z.re, -z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_one' := by apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' a b := by apply QuadraticAlgebra.ext <;> simp <;> ring
  map_mul' a b := by apply QuadraticAlgebra.ext <;> simp <;> ring

@[simp] theorem rho_re (z : QAlg) : (rho z).re = z.re := rfl
@[simp] theorem rho_im (z : QAlg) : (rho z).im = -z.im := rfl
@[simp] theorem rho_x : rho x = x := by apply QuadraticAlgebra.ext <;> simp
@[simp] theorem rho_w : rho w = -w := by apply QuadraticAlgebra.ext <;> simp
@[simp] theorem rho_involution (z : QAlg) : rho (rho z) = z := by apply QuadraticAlgebra.ext <;> simp

def rhoEquiv : QAlg ≃+* QAlg := { rho with invFun := rho, left_inv := rho_involution, right_inv := rho_involution }

theorem rho_partial (z : QAlg) : rho (delta z) = delta (rho z) := by
  apply QuadraticAlgebra.ext <;> simp [derivative_neg] <;> ring

/-- Substitution by `-X` on rational polynomials. -/
def flip : QPoly →+* QPoly := Polynomial.eval₂RingHom Polynomial.C (-X)

theorem flip_apply (p : QPoly) : flip p = p.comp (-X) := rfl
@[simp] theorem flip_X : flip X = -X := by simp [flip_apply]
@[simp] theorem flip_q : flip q = q := by simp [q, map_add, map_pow, flip_apply]
@[simp] theorem flip_involution (p : QPoly) : flip (flip p) = p :=
  Polynomial.comp_neg_X_comp_neg_X p

theorem derivative_flip (p : QPoly) : derivative (flip p) = -flip (derivative p) := by
  simp [flip_apply, derivative_comp, derivative_neg]

def tau : QAlg →+* QAlg where
  toFun z := ⟨flip z.re, -flip z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_one' := by apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' a b := by apply QuadraticAlgebra.ext <;> simp [map_add] <;> ring
  map_mul' a b := by apply QuadraticAlgebra.ext <;> simp [map_add, map_mul] <;> ring

@[simp] theorem tau_re (z : QAlg) : (tau z).re = flip z.re := rfl
@[simp] theorem tau_im (z : QAlg) : (tau z).im = -flip z.im := rfl
@[simp] theorem tau_x : tau x = -x := by apply QuadraticAlgebra.ext <;> simp
@[simp] theorem tau_w : tau w = -w := by apply QuadraticAlgebra.ext <;> simp
@[simp] theorem tau_involution (z : QAlg) : tau (tau z) = z := by apply QuadraticAlgebra.ext <;> simp

def tauEquiv : QAlg ≃+* QAlg := { tau with invFun := tau, left_inv := tau_involution, right_inv := tau_involution }

theorem tau_partial (z : QAlg) : tau (delta z) = -delta (tau z) := by
  apply QuadraticAlgebra.ext <;> simp [map_sub, map_mul, derivative_neg, derivative_flip]

/-- The actual midpoint evaluation `x=0,w=1`. -/
def midpoint : QAlg →+* ℚ where
  toFun z := z.re.eval 0 + z.im.eval 0
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' a b := by simp; ring
  map_mul' a b := by simp [q]; ring

@[simp] theorem midpoint_apply (z : QAlg) : midpoint z = z.re.eval 0 + z.im.eval 0 := rfl
@[simp] theorem midpoint_x : midpoint x = 0 := by simp
@[simp] theorem midpoint_w : midpoint w = 1 := by simp
@[simp] theorem midpoint_C (p : QPoly) : midpoint (C p) = p.eval 0 := by simp

/-- Coefficientwise integer-to-rational polynomial embedding. -/
def zmap : Midpoint.ZPoly →+* QPoly := Polynomial.mapRingHom (Int.castRingHom ℚ)

@[simp] theorem zmap_coeff (p : Midpoint.ZPoly) (k : ℕ) :
    (zmap p).coeff k = (p.coeff k : ℚ) := by simp [zmap]
@[simp] theorem zmap_X : zmap Polynomial.X = Polynomial.X := by simp [zmap]
@[simp] theorem zmap_q : zmap Midpoint.q = q := by simp [Midpoint.q, q, map_add, map_pow]

theorem zmap_derivative (p : Midpoint.ZPoly) :
    zmap (derivative p) = derivative (zmap p) := by
  exact Polynomial.derivative_map p (Int.castRingHom ℚ) |>.symm

theorem zmap_comp (p r : Midpoint.ZPoly) : zmap (p.comp r) = (zmap p).comp (zmap r) := by
  exact Polynomial.map_comp _ _ _

theorem zmap_injective : Function.Injective zmap := by
  intro a b h
  apply Polynomial.ext
  intro k
  have hk := congrArg (fun p : QPoly => p.coeff k) h
  simpa using hk

def lift : Midpoint.R →+* QAlg where
  toFun z := ⟨zmap z.re, zmap z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_one' := by apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' a b := by apply QuadraticAlgebra.ext <;> simp
  map_mul' a b := by apply QuadraticAlgebra.ext <;> simp [map_add, map_mul]

@[simp] theorem lift_re (z : Midpoint.R) : (lift z).re = zmap z.re := rfl
@[simp] theorem lift_im (z : Midpoint.R) : (lift z).im = zmap z.im := rfl
@[simp] theorem lift_x : lift Midpoint.x = x := by apply QuadraticAlgebra.ext <;> simp
@[simp] theorem lift_w : lift Midpoint.w = w := by apply QuadraticAlgebra.ext <;> simp
@[simp] theorem lift_C (a : Midpoint.ZPoly) : lift (Midpoint.C a) = C (zmap a) := by
  apply QuadraticAlgebra.ext <;> simp

theorem lift_injective : Function.Injective lift := by
  intro a b h
  apply QuadraticAlgebra.ext
  · exact zmap_injective (congrArg QuadraticAlgebra.re h)
  · exact zmap_injective (congrArg QuadraticAlgebra.im h)

theorem lift_delta (z : Midpoint.R) : lift (Midpoint.delta z) = delta (lift z) := by
  apply QuadraticAlgebra.ext <;> simp [map_sub, map_mul, zmap_derivative]

theorem zmap_flip (p : Midpoint.ZPoly) : zmap (Midpoint.flip p) = flip (zmap p) := by
  simp [Midpoint.flip_apply, flip_apply, zmap_comp, map_neg]

theorem lift_tau (z : Midpoint.R) : lift (Midpoint.tau z) = tau (lift z) := by
  apply QuadraticAlgebra.ext <;> simp [zmap_flip]

theorem lift_midpoint (z : Midpoint.R) : midpoint (lift z) = (Midpoint.midpoint z : ℚ) := by
  simp [midpoint_apply, Midpoint.midpoint_apply, zmap, Polynomial.eval_zero_map]

end JacobiShifted.MidpointRational
