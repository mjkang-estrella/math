import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace FairDiscrepancy

def rowEnergy {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) : ℝ :=
  ∑ j, (A i j) ^ 2

def columnEnergy {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) : ℝ :=
  ∑ i, (A i j) ^ 2

def ExactBalanced {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  A ≠ 0 ∧ (∀ i k, rowEnergy A i = rowEnergy A k) ∧
    (∀ j k, columnEnergy A j = columnEnergy A k)

def BalancedWithin {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (δ : ℝ) : Prop :=
  A ≠ 0 ∧ (∀ i k, |rowEnergy A i - rowEnergy A k| < δ) ∧
    (∀ j k, |columnEnergy A j - columnEnergy A k| < δ)

def BalancedBy {n m : ℕ} (R : ℝ → ℝ → Prop) (A : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  A ≠ 0 ∧ (∀ i k, R (rowEnergy A i) (rowEnergy A k)) ∧
    (∀ j k, R (columnEnergy A j) (columnEnergy A k))

noncomputable def rowMean {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) : ℝ :=
  (∑ j, A i j) / m

def FairRow {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) (i : Fin n) : Prop :=
  ∀ j, |rowMean A i - A i j| < ε

def A : Matrix (Fin 3) (Fin 3) ℝ := !![5, 5, 5; 1, 5, 7; 7, 5, 1]

theorem positive : ∀ i j, 0 < A i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [A]

theorem nonzero : A ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num [A] at this

theorem row_energy : ∀ i, rowEnergy A i = 75 := by
  intro i
  fin_cases i <;> norm_num [rowEnergy, A, Fin.sum_univ_succ]

theorem column_energy : ∀ j, columnEnergy A j = 75 := by
  intro j
  fin_cases j <;> norm_num [columnEnergy, A, Fin.sum_univ_succ]

theorem exact_balanced : ExactBalanced A := by
  refine ⟨nonzero, ?_, ?_⟩
  · intro i k; rw [row_energy, row_energy]
  · intro j k; rw [column_energy, column_energy]

theorem exact_implies_approximate {n m : ℕ} {B : Matrix (Fin n) (Fin m) ℝ}
    (h : ExactBalanced B) {δ : ℝ} (hδ : 0 < δ) : BalancedWithin B δ := by
  refine ⟨h.1, ?_, ?_⟩
  · intro i k; rw [h.2.1 i k, sub_self, abs_zero]; exact hδ
  · intro j k; rw [h.2.2 j k, sub_self, abs_zero]; exact hδ

theorem exact_implies_reflexive_balance {n m : ℕ} {B : Matrix (Fin n) (Fin m) ℝ}
    (h : ExactBalanced B) (R : ℝ → ℝ → Prop) (hR : ∀ x, R x x) : BalancedBy R B := by
  refine ⟨h.1, ?_, ?_⟩
  · intro i k; rw [h.2.1 i k]; exact hR _
  · intro j k; rw [h.2.2 j k]; exact hR _

theorem first_row_fair {ε : ℝ} (hε : 0 < ε) : FairRow A ε 0 := by
  intro j
  fin_cases j <;> norm_num [rowMean, A, Fin.sum_univ_succ] <;> exact hε

theorem second_row_deviation : |rowMean A 1 - A 1 0| = 10 / 3 := by
  norm_num [rowMean, A, Fin.sum_univ_succ]

theorem second_row_not_fair : ¬ FairRow A 1 1 := by
  intro h
  have h0 := h 0
  rw [second_row_deviation] at h0
  norm_num at h0

theorem main_counterexample :
    ∃ B : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, 0 < B i j) ∧ ExactBalanced B ∧
      FairRow B 1 0 ∧ ¬ FairRow B 1 1 := by
  exact ⟨A, positive, exact_balanced, first_row_fair (by norm_num), second_row_not_fair⟩

theorem not_universal_propagation :
    ¬ (∀ (n m : ℕ) (B : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ),
      0 < ε → ExactBalanced B → ∀ r, FairRow B ε r → ∀ i, FairRow B ε i) := by
  intro h
  exact second_row_not_fair (h 3 3 A 1 (by norm_num) exact_balanced 0
    (first_row_fair (by norm_num)) 1)

def scaled (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := fun i j => t * A i j

theorem scaled_positive {t : ℝ} (ht : 0 < t) : ∀ i j, 0 < scaled t i j := by
  intro i j
  exact mul_pos ht (positive i j)

theorem scaled_row_energy (t : ℝ) : ∀ i, rowEnergy (scaled t) i = 75 * t ^ 2 := by
  intro i
  fin_cases i <;> simp [rowEnergy, scaled, A, Fin.sum_univ_succ] <;> ring

theorem scaled_column_energy (t : ℝ) : ∀ j, columnEnergy (scaled t) j = 75 * t ^ 2 := by
  intro j
  fin_cases j <;> simp [columnEnergy, scaled, A, Fin.sum_univ_succ] <;> ring

theorem scaled_exact_balanced {t : ℝ} (ht : 0 < t) : ExactBalanced (scaled t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have he := congrFun (congrFun h 0) 0
    have hp := scaled_positive ht 0 0
    rw [he] at hp
    norm_num at hp
  · intro i k; rw [scaled_row_energy, scaled_row_energy]
  · intro j k; rw [scaled_column_energy, scaled_column_energy]

theorem scaled_first_row_fair (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    FairRow (scaled t) ε 0 := by
  intro j
  have hm : rowMean (scaled t) 0 = 5 * t := by
    simp [rowMean, scaled, A, Fin.sum_univ_succ]; ring
  rw [hm]
  fin_cases j <;> simpa [scaled, A, mul_comm] using hε

theorem scaled_second_row_deviation {t : ℝ} (ht : 0 ≤ t) :
    |rowMean (scaled t) 1 - scaled t 1 0| = 10 * t / 3 := by
  have he : rowMean (scaled t) 1 - scaled t 1 0 = 10 * t / 3 := by
    simp [rowMean, scaled, A, Fin.sum_univ_succ]; ring
  rw [he, abs_of_nonneg (by positivity)]

theorem every_tolerance_counterexample {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, 0 < B i j) ∧ ExactBalanced B ∧
      FairRow B ε 0 ∧ ¬ FairRow B ε 1 := by
  refine ⟨scaled ε, scaled_positive hε, scaled_exact_balanced hε,
    scaled_first_row_fair ε hε, ?_⟩
  intro h
  have h0 := h 0
  rw [scaled_second_row_deviation (le_of_lt hε)] at h0
  linarith

theorem every_tolerance_and_balance_counterexample {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ B : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, 0 < B i j) ∧ BalancedWithin B δ ∧
      FairRow B ε 0 ∧ ¬ FairRow B ε 1 := by
  obtain ⟨B, hp, hb, hf, hn⟩ := every_tolerance_counterexample hε
  exact ⟨B, hp, exact_implies_approximate hb hδ, hf, hn⟩

theorem every_reflexive_interpretation_counterexample
    (R : ℝ → ℝ → Prop) (hR : ∀ x, R x x) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, 0 < B i j) ∧ BalancedBy R B ∧
      FairRow B ε 0 ∧ ¬ FairRow B ε 1 := by
  obtain ⟨B, hp, hb, hf, hn⟩ := every_tolerance_counterexample hε
  exact ⟨B, hp, exact_implies_reflexive_balance hb R hR, hf, hn⟩

end FairDiscrepancy
