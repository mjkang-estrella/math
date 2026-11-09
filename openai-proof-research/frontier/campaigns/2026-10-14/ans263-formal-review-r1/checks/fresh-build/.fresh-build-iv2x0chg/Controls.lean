import ANS263

/- Original code by Myeongjin Kang. MIT. Concrete hypothesis-necessity controls. -/

open Finset

namespace ANS263Controls

theorem bad_probability_exponent :
    ¬ (0 < 7 * (4 / 5 : ℝ) / 2 - 3) := by norm_num

theorem negative_budget_fails :
    ¬ ((∑ _j ∈ range 0, (0 : ℝ)) ≤ (-1 : ℝ) / (1 - 1 / 2)) := by norm_num

theorem unit_ratio_unbounded (B : ℝ) :
    ∃ n : ℕ, B < ∑ j ∈ range n, (1 : ℝ) ^ j := by
  obtain ⟨n, hn⟩ := exists_nat_gt B
  exact ⟨n, by simpa using hn⟩

theorem exterior_threshold_too_small :
    ¬ ((1 / 2 : ℝ) ≤ 1 - 1 / (3 / 2)) := by norm_num

noncomputable def nonmonotoneMass (r : ℝ) : ℝ := if r = 2 then 2 else 0

theorem nonmonotone_threshold_is_zero :
    ANS263.thresholdRadius nonmonotoneMass = 0 := by
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, fun r hr => hr.1⟩
    · norm_num [nonmonotoneMass]
  · apply le_csInf
    · exact ⟨0, by norm_num [nonmonotoneMass]⟩
    · intro r hr
      exact hr.1

theorem dropping_monotonicity_breaks_bracket :
    1 < nonmonotoneMass 2 ∧ nonmonotoneMass 1 ≤ 1 ∧
    ¬ (2 ≤ ANS263.thresholdRadius nonmonotoneMass) := by
  rw [nonmonotone_threshold_is_zero]
  norm_num [nonmonotoneMass]

end ANS263Controls
