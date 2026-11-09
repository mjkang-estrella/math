import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
A strictly positive premagic matrix need not be diagonalizable.
Copyright 2026 Myeongjin Kang. Released under the MIT license.
-/

namespace PremagicCounterexample

open Matrix

/-- Standard diagonalization by an invertible change of coordinates.
The two equations on P and Q say precisely that Q is the inverse of P. -/
def Diagonalizable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : Prop :=
  ∃ (P Q : Matrix n n K) (d : n → K),
    P * Q = 1 ∧ Q * P = 1 ∧ A = P * diagonal d * Q

/-- A diagonalizable matrix has no nontrivial zero-eigenvalue Jordan chain. -/
theorem square_kernel {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n K} (hA : Diagonalizable A) {x : n → K}
    (hx : A *ᵥ (A *ᵥ x) = 0) : A *ᵥ x = 0 := by
  obtain ⟨P, Q, d, _hPQ, hQP, hdiag⟩ := hA
  have hQPvec (v : n → K) : Q *ᵥ (P *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  have hinjective {v : n → K} (hv : P *ᵥ v = 0) : v = 0 := by
    have h := congrArg (fun w => Q *ᵥ w) hv
    simpa only [hQPvec, Matrix.mulVec_zero] using h
  have hzero : diagonal d *ᵥ (diagonal d *ᵥ (Q *ᵥ x)) = 0 := by
    apply hinjective
    simpa only [hdiag, ← Matrix.mulVec_mulVec, hQPvec] using hx
  have hdzero : diagonal d *ᵥ (Q *ᵥ x) = 0 := by
    funext i
    have hi := congrFun hzero i
    simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at hi ⊢
    rcases mul_eq_zero.mp hi with hd | hd
    · simp [hd]
    · exact hd
  rw [hdiag, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdzero,
    Matrix.mulVec_zero]

/-- The concrete positive integer matrix, viewed over any field. -/
def M (K : Type*) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![4, 4, 1; 2, 2, 5; 3, 3, 3]

/-- A generalized eigenvector at zero. -/
def chainVector (K : Type*) [Field K] : Fin 3 → K := ![1, 0, -1]

/-- Its nonzero image. -/
def kernelVector (K : Type*) [Field K] : Fin 3 → K := ![3, -3, 0]

theorem chain_image (K : Type*) [Field K] :
    M K *ᵥ chainVector K = kernelVector K := by
  ext i
  fin_cases i <;> norm_num [M, chainVector, kernelVector, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]

theorem kernel_image (K : Type*) [Field K] :
    M K *ᵥ kernelVector K = 0 := by
  ext i
  fin_cases i <;> norm_num [M, kernelVector, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]

theorem not_diagonalizable (K : Type*) [Field K] [CharZero K] :
    ¬ Diagonalizable (M K) := by
  intro h
  have hs : M K *ᵥ (M K *ᵥ chainVector K) = 0 := by
    rw [chain_image, kernel_image]
  have hz := square_kernel h hs
  rw [chain_image] at hz
  have hi := congrFun hz 0
  norm_num [kernelVector] at hi

/-- Premagic means the row-sum vector equals the column-sum vector. -/
def Premagic {K : Type*} [Field K] {n : Type*} [Fintype n]
    (A : Matrix n n K) : Prop :=
  ∀ i, (∑ j, A i j) = ∑ j, A j i

theorem row_sum (K : Type*) [Field K] (i : Fin 3) :
    (∑ j, M K i j) = 9 := by
  fin_cases i <;> norm_num [M, Fin.sum_univ_succ]

theorem column_sum (K : Type*) [Field K] (i : Fin 3) :
    (∑ j, M K j i) = 9 := by
  fin_cases i <;> norm_num [M, Fin.sum_univ_succ]

theorem premagic (K : Type*) [Field K] : Premagic (M K) := by
  intro i
  rw [row_sum, column_sum]

theorem positive (i j : Fin 3) : 0 < M ℝ i j := by
  fin_cases i <;> fin_cases j <;> norm_num [M]

/-- One exact matrix simultaneously meets positivity and the premagic condition
and fails diagonalization over both the reals and the complexes. -/
theorem main_counterexample :
    (∀ i j, 0 < M ℝ i j) ∧ Premagic (M ℝ) ∧
      ¬ Diagonalizable (M ℝ) ∧ ¬ Diagonalizable (M ℂ) :=
  ⟨positive, premagic ℝ, not_diagonalizable ℝ, not_diagonalizable ℂ⟩

/-- Equivalence with the usual similarity equation `Q * A * P = diagonal d`.
The witnesses explicitly certify that `P` is invertible and `Q = P⁻¹`. -/
theorem diagonalizable_iff_similarity {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K) :
    Diagonalizable A ↔ ∃ (P Q : Matrix n n K) (d : n → K),
      P * Q = 1 ∧ Q * P = 1 ∧ Q * A * P = diagonal d := by
  constructor
  · rintro ⟨P, Q, d, hPQ, hQP, rfl⟩
    refine ⟨P, Q, d, hPQ, hQP, ?_⟩
    simp only [← mul_assoc, hQP, one_mul]
    rw [mul_assoc, hQP, mul_one]
  · rintro ⟨P, Q, d, hPQ, hQP, hd⟩
    refine ⟨P, Q, d, hPQ, hQP, ?_⟩
    rw [← hd]
    simp only [← mul_assoc, hPQ, one_mul]
    rw [mul_assoc, hPQ, mul_one]

/-- Equivalence with standard matrix notation `P⁻¹ A P = D`, with the
invertibility condition explicit so the totalized inverse is never misused. -/
theorem diagonalizable_iff_inv {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K) :
    Diagonalizable A ↔ ∃ (P : Matrix n n K) (d : n → K),
      IsUnit P ∧ P⁻¹ * A * P = diagonal d := by
  rw [diagonalizable_iff_similarity]
  constructor
  · rintro ⟨P, Q, d, hPQ, hQP, hd⟩
    have hdet : IsUnit P.det := Matrix.isUnit_det_of_right_inverse hPQ
    have hQ : Q = P⁻¹ := by
      calc
        Q = Q * (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, mul_one]
        _ = P⁻¹ := by rw [← mul_assoc, hQP, one_mul]
    exact ⟨P, d, (Matrix.isUnit_iff_isUnit_det P).mpr hdet, hQ ▸ hd⟩
  · rintro ⟨P, d, hP, hd⟩
    have hdet := (Matrix.isUnit_iff_isUnit_det P).mp hP
    exact ⟨P, P⁻¹, d, Matrix.mul_nonsing_inv P hdet,
      Matrix.nonsing_inv_mul P hdet, hd⟩

/-- Subtracting a scalar identity preserves diagonalizability. -/
theorem diagonalizable_sub_scalar {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n K} (hA : Diagonalizable A) (t : K) :
    Diagonalizable (A - t • 1) := by
  obtain ⟨P, Q, d, hPQ, hQP, hdiag⟩ := hA
  refine ⟨P, Q, fun i => d i - t, hPQ, hQP, ?_⟩
  have hd : diagonal (fun i => d i - t) = diagonal d - t • (1 : Matrix n n K) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hd]
  simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, hPQ, ← hdiag]

/-- Multiplication by any scalar preserves diagonalizability. -/
theorem diagonalizable_smul {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n K} (hA : Diagonalizable A) (c : K) :
    Diagonalizable (c • A) := by
  obtain ⟨P, Q, d, hPQ, hQP, hdiag⟩ := hA
  refine ⟨P, Q, fun i => c * d i, hPQ, hQP, ?_⟩
  have hd : diagonal (fun i => c * d i) = c • diagonal d := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hd, Matrix.mul_smul, Matrix.smul_mul, ← hdiag]

/-- Scalar translates of the counterexample, over any field. -/
def A_t (K : Type*) [Field K] (t : K) : Matrix (Fin 3) (Fin 3) K :=
  M K + t • 1

theorem A_t_not_diagonalizable (K : Type*) [Field K] [CharZero K] (t : K) :
    ¬ Diagonalizable (A_t K t) := by
  intro h
  have hh := diagonalizable_sub_scalar h t
  apply not_diagonalizable K
  simpa only [A_t, add_sub_cancel_right] using hh

theorem A_t_row_sum (K : Type*) [Field K] (t : K) (i : Fin 3) :
    (∑ j, A_t K t i j) = 9 + t := by
  fin_cases i <;> norm_num [A_t, M, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

theorem A_t_column_sum (K : Type*) [Field K] (t : K) (i : Fin 3) :
    (∑ j, A_t K t j i) = 9 + t := by
  fin_cases i <;> norm_num [A_t, M, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

theorem A_t_premagic (K : Type*) [Field K] (t : K) : Premagic (A_t K t) := by
  intro i
  rw [A_t_row_sum, A_t_column_sum]

theorem A_t_positive (t : ℝ) (ht : 0 ≤ t) (i j : Fin 3) : 0 < A_t ℝ t i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [A_t, M, Matrix.one_apply] <;> linarith

/-- A normalized positive doubly stochastic family for real `t ≥ 0`. -/
noncomputable def B_t (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (9 + t)⁻¹ • A_t ℝ t

/-- Nonnegativity and both unit-sum conditions, stated without a library convention. -/
def DoublyStochastic {n : Type*} [Fintype n] (A : Matrix n n ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ (∀ i, ∑ j, A i j = 1) ∧ (∀ j, ∑ i, A i j = 1)

theorem B_t_positive (t : ℝ) (ht : 0 ≤ t) (i j : Fin 3) : 0 < B_t t i j := by
  change 0 < (9 + t)⁻¹ * A_t ℝ t i j
  exact mul_pos (inv_pos.mpr (by linarith)) (A_t_positive t ht i j)

theorem B_t_row_sum (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) :
    (∑ j, B_t t i j) = 1 := by
  simp only [B_t, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, A_t_row_sum]
  exact inv_mul_cancel₀ (by linarith)

theorem B_t_column_sum (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) :
    (∑ j, B_t t j i) = 1 := by
  simp only [B_t, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, A_t_column_sum]
  exact inv_mul_cancel₀ (by linarith)

theorem B_t_doubly_stochastic (t : ℝ) (ht : 0 ≤ t) : DoublyStochastic (B_t t) :=
  ⟨fun i j => (B_t_positive t ht i j).le, B_t_row_sum t ht, B_t_column_sum t ht⟩

theorem B_t_premagic (t : ℝ) (ht : 0 ≤ t) : Premagic (B_t t) := by
  intro i
  rw [B_t_row_sum t ht, B_t_column_sum t ht]

theorem B_t_not_diagonalizable (t : ℝ) (ht : 0 ≤ t) : ¬ Diagonalizable (B_t t) := by
  intro h
  have hh := diagonalizable_smul h (9 + t)
  apply A_t_not_diagonalizable ℝ t
  simpa only [B_t, smul_smul, mul_inv_cancel₀ (show (9 + t : ℝ) ≠ 0 by linarith),
    one_smul] using hh

/-- A genuine existential counterexample over every characteristic-zero field. -/
theorem exists_premagic_not_diagonalizable (K : Type*) [Field K] [CharZero K] :
    ∃ A : Matrix (Fin 3) (Fin 3) K, Premagic A ∧ ¬ Diagonalizable A :=
  ⟨M K, premagic K, not_diagonalizable K⟩

theorem not_all_premagic_diagonalizable (K : Type*) [Field K] [CharZero K] :
    ¬ ∀ A : Matrix (Fin 3) (Fin 3) K, Premagic A → Diagonalizable A := by
  intro h
  exact not_diagonalizable K (h (M K) (premagic K))

theorem exists_positive_premagic_not_diagonalizable :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, 0 < A i j) ∧ Premagic A ∧ ¬ Diagonalizable A :=
  ⟨M ℝ, positive, premagic ℝ, not_diagonalizable ℝ⟩

theorem not_all_positive_premagic_diagonalizable :
    ¬ ∀ A : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, 0 < A i j) → Premagic A → Diagonalizable A := by
  intro h
  exact not_diagonalizable ℝ (h (M ℝ) positive (premagic ℝ))

theorem exists_positive_doubly_stochastic_not_diagonalizable :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, 0 < A i j) ∧ DoublyStochastic A ∧ ¬ Diagonalizable A :=
  ⟨B_t 0, B_t_positive 0 le_rfl, B_t_doubly_stochastic 0 le_rfl,
    B_t_not_diagonalizable 0 le_rfl⟩

end PremagicCounterexample
