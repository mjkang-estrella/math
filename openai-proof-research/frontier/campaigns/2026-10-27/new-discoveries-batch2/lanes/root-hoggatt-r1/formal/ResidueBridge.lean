import Mathlib

/-! Initial kernel-checked bridge for PROOF.md's q-Markov argument.
This is not a formalization of the Hoggatt theorem. -/
namespace HoggattResearch

 theorem residue_q_difference (q x r c : ℝ)
    (hq : q ≠ 1) (hx : x ≠ 0)
    (hqx : q * x - r ≠ 0) (hxr : x - r ≠ 0) :
    (c / (q * x - r) - c / (x - r)) / ((q - 1) * x) =
      -c / ((q * x - r) * (x - r)) := by
  field_simp [sub_ne_zero.mpr hq, hx, hqx, hxr]
  <;> ring

 theorem same_gap_product_pos (a b r : ℝ)
    (h : r < min a b ∨ max a b < r) :
    0 < (a - r) * (b - r) := by
  rcases h with h | h
  · exact mul_pos (sub_pos.mpr (lt_of_lt_of_le h (min_le_left _ _)))
      (sub_pos.mpr (lt_of_lt_of_le h (min_le_right _ _)))
  · exact mul_pos_of_neg_of_neg
      (sub_neg.mpr (lt_of_le_of_lt (le_max_left _ _) h))
      (sub_neg.mpr (lt_of_le_of_lt (le_max_right _ _) h))

 theorem separation_from_brackets (q y z r : ℝ)
    (hq : 0 < q) (hy : y < r) (hz : r / q < z) :
    y / q < z := by
  exact lt_trans ((div_lt_div_iff_of_pos_right hq).mpr hy) hz

#print axioms residue_q_difference
#print axioms same_gap_product_pos
#print axioms separation_from_brackets
end HoggattResearch
