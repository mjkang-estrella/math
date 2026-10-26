import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

open Matrix
open scoped ComplexOrder
namespace CstarPolynomial
noncomputable section

abbrev M₂ := Matrix (Fin 2) (Fin 2) ℂ

def A : M₂ := !![1, 2; 0, -1]
def roots : Fin 3 → M₂ := ![A, -(2 : ℂ) • A, A]
def critical : Fin 2 → M₂ := ![1, -1]

def cubic (a : Fin 3 → M₂) (z : M₂) : M₂ :=
  (z - a 0) * (z - a 1) * (z - a 2)

/-- The source's ordered deletion derivative for degree three. -/
def sourceDerivative (a : Fin 3 → M₂) (z : M₂) : M₂ :=
  (z - a 1) * (z - a 2) + (z - a 0) * (z - a 2) +
    (z - a 0) * (z - a 1)

lemma involution : A * A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, Matrix.mul_apply, Fin.sum_univ_two]

lemma centered : ∑ i, roots i = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [roots, A, Fin.sum_univ_succ]

/-- The factorization is valid for every matrix argument, without commutation. -/
theorem derivative_factorization (z : M₂) :
    sourceDerivative roots z = (3 : ℂ) • ((z - critical 0) * (z - critical 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceDerivative, roots, critical, A, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply] <;> ring

def leftMoment {n : ℕ} (a : Fin n → M₂) (p : ℕ) : M₂ :=
  ∑ i, (a i * star (a i)) ^ p

def rightMoment {n : ℕ} (a : Fin n → M₂) (p : ℕ) : M₂ :=
  ∑ i, (star (a i) * a i) ^ p

def schoenbergLeft (a : Fin 3 → M₂) (b : Fin 2 → M₂) : M₂ :=
  (1 / 9 : ℂ) • ((∑ i, a i) * star (∑ i, a i)) +
    (1 / 3 : ℂ) • leftMoment a 1 - leftMoment b 1

def schoenbergRight (a : Fin 3 → M₂) (b : Fin 2 → M₂) : M₂ :=
  (1 / 9 : ℂ) • (star (∑ i, a i) * (∑ i, a i)) +
    (1 / 3 : ℂ) • rightMoment a 1 - rightMoment b 1

def deBruinLeft (a : Fin 3 → M₂) (b : Fin 2 → M₂) : M₂ :=
  (2 / 9 : ℂ) • (leftMoment a 1) ^ 2 -
    (1 / 3 : ℂ) • leftMoment a 2 - leftMoment b 2

def deBruinRight (a : Fin 3 → M₂) (b : Fin 2 → M₂) : M₂ :=
  (2 / 9 : ℂ) • (rightMoment a 1) ^ 2 -
    (1 / 3 : ℂ) • rightMoment a 2 - rightMoment b 2

def witnessLeft : Fin 2 → ℂ := ![1, 2]
def witnessRight : Fin 2 → ℂ := ![2, -1]

lemma schoenberg_left_form :
    star witnessLeft ⬝ᵥ (schoenbergLeft roots critical *ᵥ witnessLeft) = -8 := by
  norm_num [schoenbergLeft, leftMoment, roots, critical, A, witnessLeft,
    dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.ofNat_apply, Matrix.vecMul, map_ofNat]

lemma schoenberg_right_form :
    star witnessRight ⬝ᵥ (schoenbergRight roots critical *ᵥ witnessRight) = -8 := by
  norm_num [schoenbergRight, rightMoment, roots, critical, A, witnessRight,
    dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.ofNat_apply, Matrix.vecMul, map_ofNat]

lemma deBruin_left_form :
    star witnessLeft ⬝ᵥ (deBruinLeft roots critical *ᵥ witnessLeft) = -8 := by
  norm_num [deBruinLeft, leftMoment, roots, critical, A, witnessLeft,
    dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.ofNat_apply, Matrix.vecMul, map_ofNat, pow_two, Matrix.vecHead, Matrix.vecTail]

lemma deBruin_right_form :
    star witnessRight ⬝ᵥ (deBruinRight roots critical *ᵥ witnessRight) = -8 := by
  norm_num [deBruinRight, rightMoment, roots, critical, A, witnessRight,
    dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.ofNat_apply, Matrix.vecMul, map_ofNat, pow_two, Matrix.vecHead, Matrix.vecTail]

lemma not_posSemidef_of_negative_form (D : M₂) (v : Fin 2 → ℂ)
    (h : star v ⬝ᵥ (D *ᵥ v) = -8) : ¬ D.PosSemidef := by
  intro hp
  have hh := hp.dotProduct_mulVec_nonneg v
  rw [h] at hh
  have hr : (0 : ℝ) ≤ -8 := by exact_mod_cast hh
  norm_num at hr

theorem source_counterexample_355008_355009 :
    (∑ i, roots i) = 0 ∧
    (∀ z : M₂, sourceDerivative roots z =
      (3 : ℂ) • ((z - critical 0) * (z - critical 1))) ∧
    ¬ (schoenbergLeft roots critical).PosSemidef ∧
    ¬ (schoenbergRight roots critical).PosSemidef ∧
    ¬ (deBruinLeft roots critical).PosSemidef ∧
    ¬ (deBruinRight roots critical).PosSemidef :=
  ⟨centered, derivative_factorization,
    not_posSemidef_of_negative_form _ _ schoenberg_left_form,
    not_posSemidef_of_negative_form _ _ schoenberg_right_form,
    not_posSemidef_of_negative_form _ _ deBruin_left_form,
    not_posSemidef_of_negative_form _ _ deBruin_right_form⟩

end
end CstarPolynomial
