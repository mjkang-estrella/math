import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

open scoped Matrix.Norms.Operator
open Matrix NormedSpace
namespace Novak
abbrev M₂ := Matrix (Fin 2) (Fin 2) ℂ
noncomputable def scalar (z : ℂ) : M₂ := z • (1 : M₂)
noncomputable def operatorCos (A : M₂) : M₂ :=
  (2 : ℂ)⁻¹ • (exp (Complex.I • A) + exp (-(Complex.I • A)))

lemma exp_scalar (z : ℂ) : exp (scalar z) = scalar (Complex.exp z) := by
  have hs : scalar z = diagonal (fun _ => z) := by
    ext i j; by_cases h : i = j <;> simp [scalar, h]
  rw [hs, Matrix.exp_diagonal]
  ext i j
  by_cases h : i = j <;> simp [scalar, h, Complex.exp_eq_exp_ℂ]

lemma cos_scalar (r : ℝ) : operatorCos (scalar r) = scalar (Real.cos r) := by
  unfold operatorCos
  have h₁ : Complex.I • scalar (r : ℂ) = scalar ((r : ℂ) * Complex.I) := by
    simp only [scalar, smul_smul]; congr 1; ring
  have h₂ : -(Complex.I • scalar (r : ℂ)) = scalar (-((r : ℂ) * Complex.I)) := by
    rw [h₁]; simp [scalar]
  rw [h₂, h₁, exp_scalar, exp_scalar]
  ext i j
  by_cases h : i = j
  · subst j
    simp only [scalar, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one]
    rw [Complex.ofReal_cos, Complex.cos]
    ring_nf
  · simp [scalar, h]

lemma cos_semiconj (E A B : M₂) (h : SemiconjBy E A B) :
    E * operatorCos A = operatorCos B * E := by
  have hp := (h.smul_right Complex.I).exp_right
  have hm := (h.smul_right Complex.I).neg_right.exp_right
  change E * exp (Complex.I • A) = exp (Complex.I • B) * E at hp
  change E * exp (-(Complex.I • A)) = exp (-(Complex.I • B)) * E at hm
  simp only [operatorCos, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, hp, hm]

lemma cos_square (A : M₂) (r : ℝ) (hr : r ≠ 0)
    (hsq : A * A = scalar ((r : ℂ)^2)) :
    operatorCos A = scalar (Real.cos r) := by
  have hp : SemiconjBy (scalar r + A) A (scalar r) := by
    change (scalar r + A) * A = scalar r * (scalar r + A)
    simp only [add_mul, mul_add, hsq, scalar, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, smul_smul]
    module
  have hm : SemiconjBy (scalar r - A) A (scalar (-r)) := by
    change (scalar r - A) * A = scalar (-r) * (scalar r - A)
    simp only [sub_mul, mul_sub, hsq, scalar, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, neg_smul, pow_two]
    simp only [neg_mul, smul_mul_assoc, one_mul, smul_neg, smul_smul]
    module
  have h₁ := cos_semiconj _ _ _ hp
  have h₂ := cos_semiconj _ _ _ hm
  rw [cos_scalar] at h₁
  have hneg : scalar (-(r : ℂ)) = scalar ((-r : ℝ) : ℂ) := by simp
  rw [hneg, cos_scalar, Real.cos_neg] at h₂
  have he : (scalar (r : ℂ) + A) + (scalar (r : ℂ) - A) = scalar (2*(r : ℂ)) := by
    simp only [scalar]; module
  have ht : scalar (2*(r : ℂ)) * operatorCos A =
      scalar (Real.cos r) * scalar (2*(r : ℂ)) := by
    rw [← he, add_mul, h₁, h₂, ← mul_add]
  ext i j
  have hij := congrArg (fun M : M₂ => M i j) ht
  simp only [scalar, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    Matrix.smul_apply, smul_eq_mul] at hij ⊢
  have hn : 2*(r : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast hr)
  apply mul_left_cancel₀ hn
  exact hij
end Novak
