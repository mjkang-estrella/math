import Selection

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CStarSmaleUnbounded

open Polynomial

def cubicValue {A : Type*} [CommRing A] (a : Fin 3 → A) (z : A) : A :=
  (z - a 0) * (z - a 1) * (z - a 2)

def cubicDeleted {A : Type*} [CommRing A] (a : Fin 3 → A) (z : A) : A :=
  (z - a 1) * (z - a 2) + (z - a 0) * (z - a 2) + (z - a 0) * (z - a 1)

def cubicPolynomial {A : Type*} [CommRing A] (a : Fin 3 → A) : Polynomial A :=
  (X - C (a 0)) * (X - C (a 1)) * (X - C (a 2))

theorem cubicPolynomial_eval {A : Type*} [CommRing A] (a : Fin 3 → A) (z : A) :
    (cubicPolynomial a).eval z = cubicValue a z := by
  simp [cubicPolynomial, cubicValue]

theorem cubicPolynomial_deleted {A : Type*} [CommRing A] (a : Fin 3 → A) (z : A) :
    (cubicPolynomial a).derivative.eval z = cubicDeleted a z := by
  simp [cubicPolynomial, cubicDeleted, derivative_mul]
  ring

abbrev Time := Set.Icc (0 : ℝ) 1
def timeZero : Time := ⟨0, by constructor <;> norm_num⟩
def timeOne : Time := ⟨1, by constructor <;> norm_num⟩
instance : Nonempty Time := ⟨timeZero⟩
abbrev FunctionAlgebra := C(Time, ℂ)
abbrev sourceCStarStructure : CommCStarAlgebra FunctionAlgebra := inferInstance

def coordinate : FunctionAlgebra :=
  ⟨fun t => ((2 * (t : ℝ) - 1 : ℝ) : ℂ),
    Complex.continuous_ofReal.comp ((continuous_const.mul continuous_subtype_val).sub
      continuous_const)⟩

def branch (epsilon : ℝ) : FunctionAlgebra :=
  ⟨fun t => (Real.sqrt ((2 * (t : ℝ) - 1) ^ 2 + epsilon) : ℂ),
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (((continuous_const.mul continuous_subtype_val).sub continuous_const).pow 2 |>.add
        continuous_const))⟩

def rootAmplitude (epsilon : ℝ) : FunctionAlgebra :=
  ⟨fun t => (Real.sqrt 3 : ℂ) * branch epsilon t,
    continuous_const.mul (branch epsilon).continuous⟩

def roots (epsilon : ℝ) : Fin 3 → FunctionAlgebra :=
  ![0, rootAmplitude epsilon, -rootAmplitude epsilon]

theorem branch_sq (epsilon : ℝ) (he : 0 ≤ epsilon) (t : Time) :
    branch epsilon t ^ 2 = coordinate t ^ 2 + (epsilon : ℂ) := by
  change ((Real.sqrt ((2 * (t : ℝ) - 1) ^ 2 + epsilon) : ℝ) : ℂ) ^ 2 =
    ((2 * (t : ℝ) - 1 : ℝ) : ℂ) ^ 2 + (epsilon : ℂ)
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  push_cast
  ring

theorem rootAmplitude_sq (epsilon : ℝ) (t : Time) :
    rootAmplitude epsilon t ^ 2 = 3 * branch epsilon t ^ 2 := by
  change ((Real.sqrt 3 : ℂ) * branch epsilon t) ^ 2 = _
  rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem value_eq (epsilon : ℝ) (w : FunctionAlgebra) :
    cubicValue (roots epsilon) w = w ^ 3 - 3 * branch epsilon ^ 2 * w := by
  ext t
  change (w t - 0) * (w t - rootAmplitude epsilon t) * (w t - -rootAmplitude epsilon t) =
    w t ^ 3 - 3 * branch epsilon t ^ 2 * w t
  linear_combination -(w t) * rootAmplitude_sq epsilon t

theorem deleted_eq (epsilon : ℝ) (w : FunctionAlgebra) :
    cubicDeleted (roots epsilon) w = 3 * (w - branch epsilon) * (w + branch epsilon) := by
  ext t
  change (w t - rootAmplitude epsilon t) * (w t - -rootAmplitude epsilon t) +
    (w t - 0) * (w t - -rootAmplitude epsilon t) + (w t - 0) * (w t - rootAmplitude epsilon t) =
    3 * (w t - branch epsilon t) * (w t + branch epsilon t)
  linear_combination -rootAmplitude_sq epsilon t

end CStarSmaleUnbounded

