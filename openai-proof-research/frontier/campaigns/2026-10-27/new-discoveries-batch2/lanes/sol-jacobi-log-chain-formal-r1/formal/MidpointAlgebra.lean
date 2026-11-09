import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Span

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.Midpoint
open Polynomial

abbrev ZPoly := Polynomial ℤ
def q : ZPoly := 1 + X ^ 2
abbrev R := QuadraticAlgebra ZPoly q 0

def C : ZPoly →+* R := algebraMap ZPoly R
def x : R := ⟨X, 0⟩
def w : R := ⟨0, 1⟩

@[simp] theorem C_re (p : ZPoly) : (C p).re = p := rfl
@[simp] theorem C_im (p : ZPoly) : (C p).im = 0 := rfl
@[simp] theorem x_re : x.re = X := rfl
@[simp] theorem x_im : x.im = 0 := rfl
@[simp] theorem w_re : w.re = 0 := rfl
@[simp] theorem w_im : w.im = 1 := rfl

theorem pair_mul (a b c d : ZPoly) :
    (⟨a,b⟩ : R) * ⟨c,d⟩ = ⟨a*c+q*b*d, a*d+b*c⟩ := by
  apply QuadraticAlgebra.ext <;> simp

theorem pair_eq_iff (a b c d : ZPoly) :
    (⟨a,b⟩ : R) = ⟨c,d⟩ ↔ a=c ∧ b=d := QuadraticAlgebra.ext_iff

theorem pair_normal (z : R) : z = C z.re + w * C z.im := by
  apply QuadraticAlgebra.ext <;> simp [C, w]

theorem w_sq : w ^ 2 = 1 + x ^ 2 := by
  rw [pow_two, pow_two]
  apply QuadraticAlgebra.ext
  · rw [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul]
    simp [q, QuadraticAlgebra.re_one, pow_two]
  · rw [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul]
    simp [QuadraticAlgebra.im_one]

theorem w_mul_pair (a b : ZPoly) : w * (⟨a,b⟩ : R) = ⟨q*b,a⟩ := by
  apply QuadraticAlgebra.ext <;> simp [w]

/-- The integral midpoint differential operator on actual polynomial pairs. -/
def delta : R →+ R where
  toFun z := ⟨-q * derivative z.re, -X * z.im - q * derivative z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_add' a b := by apply QuadraticAlgebra.ext <;> simp [derivative_add] <;> ring

@[simp] theorem partial_re (z : R) : (delta z).re = -q * derivative z.re := rfl
@[simp] theorem partial_im (z : R) :
    (delta z).im = -X * z.im - q * derivative z.im := rfl

@[simp] theorem derivative_q : derivative q = 2 * X := by
  simp [q, derivative_add, derivative_pow]

theorem partial_mul (a b : R) : delta (a*b) = delta a*b + a*delta b := by
  apply QuadraticAlgebra.ext <;> simp [delta, derivative_add, derivative_mul, derivative_q] <;> ring

/-- The same concrete operator, bundled as a derivation over the integers. -/
def derivation : Derivation ℤ R R :=
  Derivation.mk' delta.toIntLinearMap (fun a b => by
    change delta (a*b) = a*delta b + b*delta a
    rw [partial_mul]
    ring)

@[simp] theorem derivation_apply (z : R) : derivation z = delta z := rfl

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
def rho : R →+* R where
  toFun z := ⟨z.re, -z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_one' := by apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' a b := by apply QuadraticAlgebra.ext <;> simp <;> ring
  map_mul' a b := by apply QuadraticAlgebra.ext <;> simp <;> ring

@[simp] theorem rho_re (z : R) : (rho z).re = z.re := rfl
@[simp] theorem rho_im (z : R) : (rho z).im = -z.im := rfl
@[simp] theorem rho_x : rho x = x := by apply QuadraticAlgebra.ext <;> simp
@[simp] theorem rho_w : rho w = -w := by apply QuadraticAlgebra.ext <;> simp
@[simp] theorem rho_involution (z : R) : rho (rho z) = z := by apply QuadraticAlgebra.ext <;> simp

def rhoEquiv : R ≃+* R := { rho with invFun := rho, left_inv := rho_involution, right_inv := rho_involution }

theorem rho_partial (z : R) : rho (delta z) = delta (rho z) := by
  apply QuadraticAlgebra.ext <;> simp [derivative_neg] <;> ring

/-- Substitution by `-X` on integral polynomials. -/
def flip : ZPoly →+* ZPoly := Polynomial.eval₂RingHom Polynomial.C (-X)

theorem flip_apply (p : ZPoly) : flip p = p.comp (-X) := rfl
@[simp] theorem flip_X : flip X = -X := by simp [flip_apply]
@[simp] theorem flip_q : flip q = q := by simp [q, map_add, map_pow, flip_apply]
@[simp] theorem flip_involution (p : ZPoly) : flip (flip p) = p :=
  Polynomial.comp_neg_X_comp_neg_X p

theorem derivative_flip (p : ZPoly) : derivative (flip p) = -flip (derivative p) := by
  simp [flip_apply, derivative_comp, derivative_neg]

def tau : R →+* R where
  toFun z := ⟨flip z.re, -flip z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_one' := by apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' a b := by apply QuadraticAlgebra.ext <;> simp [map_add] <;> ring
  map_mul' a b := by apply QuadraticAlgebra.ext <;> simp [map_add, map_mul] <;> ring

@[simp] theorem tau_re (z : R) : (tau z).re = flip z.re := rfl
@[simp] theorem tau_im (z : R) : (tau z).im = -flip z.im := rfl
@[simp] theorem tau_x : tau x = -x := by apply QuadraticAlgebra.ext <;> simp
@[simp] theorem tau_w : tau w = -w := by apply QuadraticAlgebra.ext <;> simp
@[simp] theorem tau_involution (z : R) : tau (tau z) = z := by apply QuadraticAlgebra.ext <;> simp

def tauEquiv : R ≃+* R := { tau with invFun := tau, left_inv := tau_involution, right_inv := tau_involution }

theorem tau_partial (z : R) : tau (delta z) = -delta (tau z) := by
  apply QuadraticAlgebra.ext <;> simp [map_sub, map_mul, derivative_neg, derivative_flip]

/-- The actual midpoint evaluation `x=0,w=1`. -/
def midpoint : R →+* ℤ where
  toFun z := z.re.eval 0 + z.im.eval 0
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' a b := by simp; ring
  map_mul' a b := by simp [q]; ring

@[simp] theorem midpoint_apply (z : R) : midpoint z = z.re.eval 0 + z.im.eval 0 := rfl
@[simp] theorem midpoint_x : midpoint x = 0 := by simp
@[simp] theorem midpoint_w : midpoint w = 1 := by simp
@[simp] theorem midpoint_C (p : ZPoly) : midpoint (C p) = p.eval 0 := by simp

/-- Integral principal-ideal membership, expressed without any quotient. -/
def InW (z : R) : Prop := ∃ y : R, z = w*y

theorem inW_iff (z : R) : InW z ↔ q ∣ z.re := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.im, by simp [w]⟩
  · rintro ⟨b, hb⟩
    refine ⟨⟨z.im,b⟩, ?_⟩
    apply QuadraticAlgebra.ext <;> simp [w, hb]

theorem inW_ideal_span (z : R) : InW z ↔ z ∈ Ideal.span ({w} : Set R) := by
  rw [Ideal.mem_span_singleton]
  rfl

theorem inW_zero : InW 0 := ⟨0, by simp⟩
theorem inW_add {a b : R} (ha : InW a) (hb : InW b) : InW (a+b) := by
  rcases ha with ⟨a,rfl⟩; rcases hb with ⟨b,rfl⟩
  exact ⟨a+b, (mul_add _ _ _).symm⟩
theorem inW_neg {a : R} (ha : InW a) : InW (-a) := by
  rcases ha with ⟨a,rfl⟩
  exact ⟨-a, by ring⟩
theorem inW_mul_right {a : R} (ha : InW a) (b : R) : InW (a*b) := by
  rcases ha with ⟨a,rfl⟩
  exact ⟨a*b, by ring⟩
theorem inW_partial {a : R} (ha : InW a) : InW (delta a) := by
  rcases ha with ⟨a,rfl⟩
  rw [partial_mul, partial_w]
  exact ⟨-x*a+delta a, by ring⟩

end JacobiShifted.Midpoint
