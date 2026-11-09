import Diagonal

open Finset Set

namespace Lachaume

noncomputable def elementary (v : Fin 4 → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (univ : Finset (Fin 4)).powersetCard k, ∏ i ∈ S, v i

noncomputable def symmetric (v : Fin 4 → ℝ) : ℝ :=
  elementary v 0 + 2 * elementary v 1 + elementary v 2 +
    2 * elementary v 3 + elementary v 4

def positiveOrthant : Set (Fin 4 → ℝ) := {v | ∀ i, 0 < v i}

noncomputable def symmetricRoot (v : Fin 4 → ℝ) : ℝ := fourthRoot (symmetric v)

noncomputable def slice (t : ℝ) : Fin 4 → ℝ := ![2, t, t, t]

theorem subsets_one : (univ : Finset (Fin 4)).powersetCard 1 =
    {{0}, {1}, {2}, {3}} := by decide +kernel
theorem subsets_two : (univ : Finset (Fin 4)).powersetCard 2 =
    {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} := by decide +kernel
theorem subsets_three : (univ : Finset (Fin 4)).powersetCard 3 =
    {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}} := by decide +kernel
theorem subsets_four : (univ : Finset (Fin 4)).powersetCard 4 =
    {{0, 1, 2, 3}} := by decide +kernel

theorem symmetric_expansion (v : Fin 4 → ℝ) : symmetric v =
    1 + 2 * (v 0 + v 1 + v 2 + v 3) +
    (v 0 * v 1 + v 0 * v 2 + v 0 * v 3 + v 1 * v 2 + v 1 * v 3 + v 2 * v 3) +
    2 * (v 0 * v 1 * v 2 + v 0 * v 1 * v 3 + v 0 * v 2 * v 3 + v 1 * v 2 * v 3) +
    v 0 * v 1 * v 2 * v 3 := by
  unfold symmetric elementary
  rw [subsets_one, subsets_two, subsets_three, subsets_four]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton,
    Finset.powersetCard_zero, Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]
  ring

theorem elementary_eq_mathlib (v : Fin 4 → ℝ) (k : ℕ) :
    elementary v k = MvPolynomial.eval v (MvPolynomial.esymm (Fin 4) ℝ k) := by
  simp [elementary, MvPolynomial.esymm]

theorem symmetric_pos {v : Fin 4 → ℝ} (hv : v ∈ positiveOrthant) : 0 < symmetric v := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  rw [symmetric_expansion]
  positivity

theorem symmetric_diagonal (x : ℝ) : symmetric (fun _ => x) = quartic x := by
  rw [symmetric_expansion]
  dsimp [quartic]
  ring

theorem symmetric_slice (t : ℝ) : symmetric (slice t) = 5 + 12 * t + 15 * t ^ 2 + 4 * t ^ 3 := by
  rw [symmetric_expansion]
  norm_num [slice]
  ring

theorem slice_pos {t : ℝ} (ht : 0 < t) : slice t ∈ positiveOrthant := by
  intro i
  fin_cases i <;> norm_num [slice] <;> exact ht

theorem slice_midpoint : (1 / 2 : ℝ) • slice (1 / 20) + (1 / 2 : ℝ) • slice (3 / 20) =
    slice (1 / 10) := by
  ext i
  fin_cases i <;> norm_num [slice]

theorem slice_left_value : symmetric (slice (1 / 20)) = 2819 / 500 := by
  rw [symmetric_slice]
  norm_num

theorem slice_middle_value : symmetric (slice (1 / 10)) = 3177 / 500 := by
  rw [symmetric_slice]
  norm_num

theorem slice_right_value : symmetric (slice (3 / 20)) = 7151 / 1000 := by
  rw [symmetric_slice]
  norm_num

theorem strict_midpoint_violation :
    symmetricRoot ((1 / 2 : ℝ) • slice (1 / 20) + (1 / 2 : ℝ) • slice (3 / 20)) <
      (1 / 2 : ℝ) * symmetricRoot (slice (1 / 20)) +
        (1 / 2 : ℝ) * symmetricRoot (slice (3 / 20)) := by
  have hl : (15409 / 10000 : ℝ) < fourthRoot (2819 / 500) :=
    rational_lt_fourthRoot (by norm_num) (by norm_num) (by norm_num)
  have hm : fourthRoot (3177 / 500) < (15877 / 10000 : ℝ) :=
    fourthRoot_lt_rational (by norm_num) (by norm_num) (by norm_num)
  have hr : (16352 / 10000 : ℝ) < fourthRoot (7151 / 1000) :=
    rational_lt_fourthRoot (by norm_num) (by norm_num) (by norm_num)
  rw [slice_midpoint]
  unfold symmetricRoot
  rw [slice_left_value, slice_middle_value, slice_right_value]
  linarith

theorem symmetricRoot_not_concave : ¬ ConcaveOn ℝ positiveOrthant symmetricRoot := by
  intro h
  have hc := h.2 (slice_pos (show (0 : ℝ) < 1 / 20 by norm_num))
    (slice_pos (show (0 : ℝ) < 3 / 20 by norm_num))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  exact (not_lt_of_ge hc) strict_midpoint_violation

noncomputable def sourceCoefficient : Fin 5 → ℝ := ![1, 2, 1, 2, 1]

noncomputable def sourceFunction (v : Fin 4 → ℝ) : ℝ :=
  ∑ k : Fin 5, sourceCoefficient k * elementary v k.val

theorem sourceCoefficient_positive (k : Fin 5) : 0 < sourceCoefficient k := by
  fin_cases k <;> norm_num [sourceCoefficient]

theorem sourceFunction_eq (v : Fin 4 → ℝ) : sourceFunction v = symmetric v := by
  simp [sourceFunction, sourceCoefficient, Fin.sum_univ_succ, symmetric]
  ring

theorem sourceFunction_contDiff : ContDiff ℝ 2 sourceFunction := by
  rw [show sourceFunction = (fun v => symmetric v) from funext sourceFunction_eq]
  simp_rw [symmetric_expansion]
  fun_prop

theorem sourceFunction_root_contDiffOn : ContDiffOn ℝ 2
    (fun v => (sourceFunction v) ^ (1 / 4 : ℝ)) positiveOrthant := by
  intro v hv
  have hp : 0 < sourceFunction v := by
    rw [sourceFunction_eq]
    exact symmetric_pos hv
  exact ((Real.contDiffAt_rpow_const_of_ne (p := (1 / 4 : ℝ)) (ne_of_gt hp)).comp v
    sourceFunction_contDiff.contDiffAt).contDiffWithinAt

theorem source_diagonal_concavity_counterexample :
    (∀ k : Fin 5, 0 < sourceCoefficient k) ∧
    (∀ v ∈ positiveOrthant, 0 < sourceFunction v) ∧
    ContDiffOn ℝ 2 (fun v => (sourceFunction v) ^ (1 / 4 : ℝ)) positiveOrthant ∧
    ConcaveOn ℝ (Ioi 0) (fun x : ℝ => (sourceFunction (fun _ => x)) ^ (1 / 4 : ℝ)) ∧
    ¬ ConcaveOn ℝ positiveOrthant (fun v => (sourceFunction v) ^ (1 / 4 : ℝ)) := by
  refine ⟨sourceCoefficient_positive, ?_, sourceFunction_root_contDiffOn, ?_, ?_⟩
  · intro v hv
    rw [sourceFunction_eq]
    exact symmetric_pos hv
  · simp only [sourceFunction_eq, symmetric_diagonal]
    exact diagonal_concave
  · simp only [sourceFunction_eq]
    exact symmetricRoot_not_concave

end Lachaume
