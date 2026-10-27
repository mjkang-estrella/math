import Selection

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CStarSmale

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

def SourceCubicClaim (A : Type*) [NormedCommRing A] : Prop :=
  ∀ (a : Fin 3 → A) (z : A), cubicDeleted a z ≠ 0 →
    ∃ w : A, cubicDeleted a w = 0 ∧
      ‖cubicValue a z - cubicValue a w‖ / ‖z - w‖ ≤ ‖cubicDeleted a z‖

abbrev Time := Set.Icc (0 : ℝ) 1
def timeZero : Time := ⟨0, by constructor <;> norm_num⟩
def timeOne : Time := ⟨1, by constructor <;> norm_num⟩
instance : Nonempty Time := ⟨timeZero⟩
abbrev FunctionAlgebra := C(Time, ℂ)

def coordinate : FunctionAlgebra :=
  ⟨fun t => ((2 * (t : ℝ) - 1 : ℝ) : ℂ),
    Complex.continuous_ofReal.comp ((continuous_const.mul continuous_subtype_val).sub
      continuous_const)⟩

def branch : FunctionAlgebra :=
  ⟨fun t => (Real.sqrt ((2 * (t : ℝ) - 1) ^ 2 + 1 / 16) : ℂ),
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (((continuous_const.mul continuous_subtype_val).sub continuous_const).pow 2 |>.add
        continuous_const))⟩

def rootAmplitude : FunctionAlgebra :=
  ⟨fun t => (Real.sqrt 3 : ℂ) * branch t, continuous_const.mul branch.continuous⟩

def roots : Fin 3 → FunctionAlgebra := ![0, rootAmplitude, -rootAmplitude]

theorem branch_sq (t : Time) : branch t ^ 2 = coordinate t ^ 2 + (1 / 16 : ℂ) := by
  change ((Real.sqrt ((2 * (t : ℝ) - 1) ^ 2 + 1 / 16) : ℝ) : ℂ) ^ 2 =
    ((2 * (t : ℝ) - 1 : ℝ) : ℂ) ^ 2 + (1 / 16 : ℂ)
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  push_cast
  ring

theorem rootAmplitude_sq (t : Time) : rootAmplitude t ^ 2 = 3 * branch t ^ 2 := by
  change ((Real.sqrt 3 : ℂ) * branch t) ^ 2 = _
  rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem value_eq (w : FunctionAlgebra) :
    cubicValue roots w = w ^ 3 - 3 * branch ^ 2 * w := by
  ext t
  simp only [cubicValue, roots, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.zero_apply, ContinuousMap.pow_apply]
  have h := rootAmplitude_sq t
  change (w t - 0) * (w t - rootAmplitude t) * (w t - -rootAmplitude t) =
    w t ^ 3 - 3 * branch t ^ 2 * w t
  linear_combination -(w t) * h

theorem deleted_eq (w : FunctionAlgebra) :
    cubicDeleted roots w = 3 * (w - branch) * (w + branch) := by
  ext t
  change (w t - rootAmplitude t) * (w t - -rootAmplitude t) +
    (w t - 0) * (w t - -rootAmplitude t) + (w t - 0) * (w t - rootAmplitude t) =
    3 * (w t - branch t) * (w t + branch t)
  have h := rootAmplitude_sq t
  linear_combination -h

end CStarSmale
