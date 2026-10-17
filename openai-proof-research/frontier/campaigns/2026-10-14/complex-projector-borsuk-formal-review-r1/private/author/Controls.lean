import BorsukLocal

/- Copyright 2026 Myeongjin Kang. MIT. Exact witnesses and false-variant controls. -/
namespace BorsukControls
open BorsukLocal

theorem origin_margin : (1/50 : ℝ)/25 < max (favored 0 0 (1/50)) (other 0 0 (1/50)) := by
  apply two_trio_margin <;> norm_num

theorem equality_first_case : (9/25 : ℝ)*(1/50) ≤ favored (1/10000) (1/100) (1/50) := by
  apply favored_case <;> norm_num

theorem equality_large_boundary : (353/500 : ℝ)*(1/100) < other 0 (1/25) (1/100) := by
  apply other_large_case <;> norm_num

theorem small_scale_case : (1/50 : ℝ)/25 < favored 0 (1/100) (1/50) := by
  apply favored_small_case <;> norm_num

theorem three_chart_witnesses :
    (0:ℝ)^2+(0:ℝ)^2 < radius^2 ∧
    (1/10000:ℝ)^2+(1/100:ℝ)^2 < radius^2 ∧
    (0:ℝ)^2+(1/25:ℝ)^2 < radius^2 := by
  rw [radius_sq]
  norm_num

theorem zero_epsilon_obstruction :
    max (favored 0 0 0) (other 0 0 0) = 0 := by
  norm_num [favored, other]

theorem excessive_epsilon_obstruction :
    max (favored 0 0 (1/4)) (other 0 0 (1/4)) < 0 := by
  norm_num [favored, other]

theorem negative_magnitude_obstruction :
    max (favored (-1) 0 (1/50)) (other (-1) 0 (1/50)) < 0 := by
  norm_num [favored, other]

theorem outside_chart_obstruction :
    max (favored 2 2 (1/50)) (other 2 2 (1/50)) < 0 := by
  norm_num [favored, other]

theorem favored_margin_is_tight :
    favored 0 0 (1/50) = (9/25 : ℝ)*(1/50) := by norm_num [favored]

theorem overly_strong_other_margin_false :
    other 0 (1/25) (1/100) < (4/5 : ℝ)*(1/100) := by norm_num [other]

theorem conjugate_is_essential :
    ((starRingEnd ℂ (1+Complex.I))*Complex.I).re = 1 ∧
    ((1+Complex.I)*Complex.I).re = -1 := by norm_num

theorem strict_cap_boundary :
    (1/2 : ℝ)+(1/2 : ℝ) ≤ 1 ∧ ¬ (0:ℝ) < 0 := by norm_num

end BorsukControls
