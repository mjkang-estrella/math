import DerivativeSign

open Polynomial
open scoped BigOperators

namespace MillsCounterexample

theorem witnessPoly_negative (t : ℝ) (ha : (lowerEndpoint : ℝ) < t)
    (hb : t < (upperEndpoint : ℝ)) :
    witnessPoly.eval₂ (Int.castRingHom ℝ) t < 0 := by
  let z : ℝ := (t - (lowerEndpoint : ℝ)) / ((upperEndpoint - lowerEndpoint : ℚ) : ℝ)
  have hw : (0 : ℝ) < ((upperEndpoint - lowerEndpoint : ℚ) : ℝ) := by
    norm_num [upperEndpoint, lowerEndpoint]
  have hz0 : 0 < z := div_pos (sub_pos.mpr ha) hw
  have hz1 : z < 1 := by
    apply (div_lt_one hw).mpr
    push_cast
    linarith
  have he : (lowerEndpoint : ℝ) + ((upperEndpoint - lowerEndpoint : ℚ) : ℝ) * z = t := by
    dsimp [z]
    field_simp
    ring
  have hid := bernstein_identity z
  rw [he] at hid
  rw [hid]
  apply Finset.sum_neg
  · intro k _
    have hc : (bernsteinScaled k : ℝ) < 0 := by
      exact_mod_cast bernsteinScaled_negative k
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc (pow_pos hz0 k.1))
      (pow_pos (sub_pos.mpr hz1) (21 - k.1))
  · exact Finset.univ_nonempty

theorem witnessPoly_pi_negative :
    witnessPoly.eval₂ (Int.castRingHom ℝ) (Real.pi / 2) < 0 := by
  apply witnessPoly_negative
  · have h := Real.pi_gt_d6
    norm_num [lowerEndpoint]
    linarith
  · have h := Real.pi_lt_d6
    norm_num [upperEndpoint]
    linarith

end MillsCounterexample
