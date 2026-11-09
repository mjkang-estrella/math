import Tail
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace BesselFejer

lemma series_pos_of_partial (q : ℝ) (hq : |q| ≤ 9)
    (hp : 2*(9 : ℝ)^20 / ((20 : ℕ).factorial : ℝ)^2 <
      ∑ n ∈ Finset.range 20, term n q) : 0 < series q := by
  have h := (abs_le.mp (series_error q hq)).1
  linarith

lemma series_neg_of_partial (q : ℝ) (hq : |q| ≤ 9)
    (hp : (∑ n ∈ Finset.range 20, term n q) <
      -(2*(9 : ℝ)^20 / ((20 : ℕ).factorial : ℝ)^2)) : series q < 0 := by
  have h := (abs_le.mp (series_error q hq)).2
  linarith

lemma rootAL_positive : 0 < besselJ0 (24048/10000) := by
  apply series_pos_of_partial
  · norm_num
  · norm_num [term, Finset.sum_range_succ, Nat.factorial]

lemma rootAU_negative : besselJ0 (24049/10000) < 0 := by
  apply series_neg_of_partial
  · norm_num
  · norm_num [term, Finset.sum_range_succ, Nat.factorial]

lemma rootBL_negative : besselJ0 (55200/10000) < 0 := by
  apply series_neg_of_partial
  · norm_num
  · norm_num [term, Finset.sum_range_succ, Nat.factorial]

lemma rootBU_positive : 0 < besselJ0 (55201/10000) := by
  apply series_pos_of_partial
  · norm_num
  · norm_num [term, Finset.sum_range_succ, Nat.factorial]

end BesselFejer
