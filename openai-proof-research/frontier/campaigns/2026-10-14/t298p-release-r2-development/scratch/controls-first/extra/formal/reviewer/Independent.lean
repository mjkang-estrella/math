import T298P

namespace T298PReview
noncomputable section
open scoped BigOperators

def C (q a : Fin 2) : ℝ := ![![(3:ℝ)/5, 4/5], ![-4/5, 3/5]] q a
def xi (a : Fin 2) : ℝ := ![(1:ℝ), 2] a

theorem real_column_gram (a b : Fin 2) :
    ∑ q, C q a * C q b = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [C, Fin.sum_univ_two]

theorem nonorthogonal : inner ℝ (xi 0) (xi 1) = (2:ℝ) := by
  norm_num [xi]

theorem nonorthogonal_isometry :
    ∑ q, ‖∑ a, C q a • xi a‖^2 = (5:ℝ) := by
  rw [T298P.coefficient_isometry C xi real_column_gram]
  norm_num [xi, Fin.sum_univ_two, Real.norm_eq_abs]

theorem positive_energy :
    ∑ q, ‖(1 / ((3:ℝ) * 2^2)) • (∑ a, C q a • xi a)‖^2 = (5:ℝ)/144 := by
  rw [T298P.leading_score_energy C xi real_column_gram]
  norm_num [xi, Fin.sum_univ_two, Real.norm_eq_abs]

theorem zero_epsilon_total_division :
    ∑ q, ‖(1 / ((0:ℝ) * 2^2)) • (∑ a, C q a • xi a)‖^2 = (0:ℝ) := by
  simp

theorem bad_gram_changes_energy :
    (∑ _q : Fin 2, ‖∑ a : Fin 2, (1:ℝ) • xi a‖^2) ≠ ∑ a : Fin 2, ‖xi a‖^2 := by
  norm_num [xi, Fin.sum_univ_two, Real.norm_eq_abs]

-- All hypotheses of strict_gap hold on an explicit finite-real model.
theorem nonvacuous_strict_gap : (0:ℝ) < 3/4 := by
  apply T298P.strict_gap 1 (1/8) (1/8) 0 (7/8) (3/4) (7/8) 0 1 2 2 <;> norm_num

-- Each witness includes the retained analytic interfaces and negated conclusion.
theorem endpoint_is_needed :
    (1:ℝ) > 0 ∧ (0:ℝ) ≥ 0 ∧
    1*(1-0)-0 ≤ (1:ℝ)-0 ∧ (0:ℝ)-0 ≤ 1*(1-1)+0 ∧
    ¬ ((1:ℝ) ≤ 0) ∧ ¬ (1*((1-0)-(1-1))-(0+0) ≤ (0:ℝ)-0) := by
  norm_num

theorem reversed_gap_is_false :
    (0:ℝ) ≤ 0 ∧ 1*(0-1)-0 ≤ (0:ℝ)-1 ∧ (0:ℝ)-0 ≤ 1*(1-1)+0 ∧
    1*((1-1)-(1-0))-(0+0) ≤ (0:ℝ)-1 ∧
    ¬ (1*((1-0)-(1-1))-(0+0) ≤ (0:ℝ)-1) := by
  norm_num

theorem weak_error_allows_equality :
    (1:ℝ)>0 ∧ (1:ℝ)≥0 ∧ (0:ℝ)≥0 ∧ (0:ℝ)≤0 ∧
    1*(1-0)-1 ≤ (0:ℝ)-0 ∧ (0:ℝ)-0 ≤ 1*(2-2)+0 ∧
    (0:ℝ)<2-0 ∧ (2-1:ℝ)≤(2-0)/2 ∧
    (1:ℝ)+0 ≤ 1*(2-0)/2 ∧ ¬ ((0:ℝ)<0) := by
  norm_num

end
end T298PReview
