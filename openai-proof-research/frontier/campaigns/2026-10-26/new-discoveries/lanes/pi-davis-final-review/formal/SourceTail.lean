import QuotientBridge

namespace Davis

theorem source_tail {d : ℕ} {x : ℝ} (hd : 43 ≤ d)
    (hx : ((d : ℝ) + Real.sqrt (d + 2)) / 2 ≤ x) :
    (199 / 200 : ℝ) * (d - 2) / (2 * x + d - 2) < -remainder d x / P d x := by
  have hdr : (43 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 ≤ Real.sqrt (d + 2 : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (d + 2 : ℝ)) ^ 2 = (d : ℝ) + 2 :=
    Real.sq_sqrt (by positivity)
  have hsg : 2 ≤ Real.sqrt (d + 2 : ℝ) := by nlinarith
  have hhalf : (d : ℝ) / 2 < x := by linarith
  have ha : 1 ≤ x - d / 2 := by linarith
  have hasq : (d : ℝ) + 2 ≤ 4 * (x - d / 2) ^ 2 := by nlinarith
  have hm := moment_identity hhalf
  have hV := centralMoment_two_nonneg d x
  have hM := moment_four_ge_sq hhalf
  have hbound := tail_variance_bound hdr ha hasq hV hM hm
  have hp : (d + 1 : ℝ) ≠ 0 := by positivity
  have hden : 0 < 2 * x + d - 2 := by linarith
  have hdenA : x - (d : ℝ) / 2 + d - 1 ≠ 0 := by linarith
  rw [remainder_ratio_moment hhalf]
  have heq : ((d : ℝ) - 4 * centralMoment d x 2) / (2 * (d + 1)) -
      (199 / 200 : ℝ) * (d - 2) / (2 * x + d - 2) =
      2 / (d + 1 : ℝ) * (varianceTarget d (x - d / 2) - centralMoment d x 2) := by
    dsimp [varianceTarget]
    rw [show x - (d : ℝ) / 2 + d - 1 = (2 * x + d - 2) / 2 by ring]
    field_simp
    ring
  have hpos : 0 < 2 / (d + 1 : ℝ) *
      (varianceTarget d (x - d / 2) - centralMoment d x 2) := by
    apply mul_pos
    · positivity
    · exact sub_pos.mpr hbound
  rw [← heq] at hpos
  linarith

end Davis
