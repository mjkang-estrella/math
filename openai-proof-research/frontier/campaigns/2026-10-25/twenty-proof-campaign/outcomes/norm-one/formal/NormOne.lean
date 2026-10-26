import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace NormOneCounterexample

open Matrix

def J (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K := !![1, 1; 1, 1]

def IsEigenpair {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K)
    (mu : K) (v : Fin 2 → K) : Prop := v ≠ 0 ∧ A *ᵥ v = mu • v

theorem spectrum {K : Type*} [Field K] (mu : K) (v : Fin 2 → K)
    (h : IsEigenpair (J K) mu v) : mu = 0 ∨ mu = 2 := by
  obtain ⟨hne, heq⟩ := h
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  norm_num [J, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
  by_cases hs : v 0 + v 1 = 0
  · left
    by_contra hl
    have hz0 : v 0 = 0 := (mul_eq_zero.mp (h0.symm.trans hs)).resolve_left hl
    have hz1 : v 1 = 0 := (mul_eq_zero.mp (h1.symm.trans hs)).resolve_left hl
    apply hne
    funext i
    fin_cases i <;> assumption
  · right
    have hz : (mu - 2) * (v 0 + v 1) = 0 := by linear_combination -h0 - h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hs)

theorem complex_spectral_bound (mu : ℂ) (v : Fin 2 → ℂ)
    (h : IsEigenpair (J ℂ) mu v) : ‖mu‖ ≤ 2 := by
  rcases spectrum mu v h with rfl | rfl <;> norm_num

noncomputable def w : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![2, 2]

theorem w_apply (i : Fin 2) : w i = 2 := by
  fin_cases i <;> rfl

theorem eigenpair : IsEigenpair (J ℝ) 2 w := by
  constructor
  · intro h
    have h0 := congrArg (fun v : Fin 2 → ℝ => v 0) h
    norm_num [w] at h0
  · ext i
    fin_cases i <;> norm_num [J, w, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem norm_square : ‖w‖ ^ 2 = 8 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  norm_num [w, Fin.sum_univ_succ]

theorem norm_ne_one : ‖w‖ ≠ 1 := by
  intro h
  have hh := norm_square
  rw [h] at hh
  norm_num at hh

noncomputable def frobeniusNorm (v : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

theorem frobenius_ne_one : frobeniusNorm w ≠ 1 := by
  intro h
  have hs : ∑ i, w i ^ 2 = (8 : ℝ) := by norm_num [w, Fin.sum_univ_succ]
  have hh : (Real.sqrt (8 : ℝ)) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have he : Real.sqrt (8 : ℝ) = 1 := by
    unfold frobeniusNorm at h
    rw [hs] at h
    exact h
  rw [he] at hh
  norm_num at hh

theorem positive (i j : Fin 2) : 0 < J ℝ i j := by
  fin_cases i <;> fin_cases j <;> norm_num [J]

theorem premagic (i : Fin 2) : (∑ j, J ℝ i j) = ∑ j, J ℝ j i := by
  fin_cases i <;> norm_num [J, Fin.sum_univ_succ]

/-- The matrix is strictly positive and premagic; its displayed eigenpair is
dominant even when all complex eigenvalues are considered, but neither norm
of that eigenvector is one. -/
theorem main_counterexample :
    (∀ i j, 0 < J ℝ i j) ∧
    (∀ i, (∑ j, J ℝ i j) = ∑ j, J ℝ j i) ∧
    IsEigenpair (J ℝ) 2 w ∧
    (∀ mu v, IsEigenpair (J ℂ) mu v → ‖mu‖ ≤ 2) ∧
    ‖w‖ ≠ 1 ∧ frobeniusNorm w ≠ 1 :=
  ⟨positive, premagic, eigenpair, complex_spectral_bound, norm_ne_one, frobenius_ne_one⟩

end NormOneCounterexample
