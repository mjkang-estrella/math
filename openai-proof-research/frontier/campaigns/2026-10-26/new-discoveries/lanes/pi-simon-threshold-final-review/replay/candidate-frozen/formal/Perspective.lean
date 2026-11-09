import ThresholdDefs
noncomputable section
open Set Real
namespace SimonThreshold
lemma kernel_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt kernel (-(exp t - 1)⁻¹) t := by
  have he : exp (-t) < 1 := by rw [exp_lt_one_iff]; linarith
  have hp : 0 < 1 - exp (-t) := sub_pos.mpr he
  have hd := (((hasDerivAt_id t).neg.exp).const_sub 1).log (ne_of_gt hp)
  have hz : exp t ≠ 0 := ne_of_gt (exp_pos t)
  have h1 : exp t - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (one_lt_exp_iff.mpr ht))
  convert hd.neg using 1
  · rfl
  · change -(exp t - 1)⁻¹ = -(-(exp (-t) * (-1)) / (1 - exp (-t)))
    rw [exp_neg]
    field_simp [hz, h1]

lemma kernel_strictConvex : StrictConvexOn ℝ (Ioi (0 : ℝ)) kernel := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
  · intro x hx
    exact (kernel_hasDerivAt hx).continuousAt.continuousWithinAt
  · simp only [interior_Ioi]
    intro x hx y hy hxy
    rw [(kernel_hasDerivAt hx).deriv, (kernel_hasDerivAt hy).deriv]
    apply neg_lt_neg
    apply inv_strictAnti₀ (sub_pos.mpr (one_lt_exp_iff.mpr hx))
    exact sub_lt_sub_right (exp_lt_exp.mpr hxy) 1
/-- Elementary positive perspective, with an explicit fixed positive numerator. -/
lemma perspective_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi (0 : ℝ)) f)
    {s : ℝ} (hs : 0 < s) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (fun a => a * f (s / a)) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [mem_Ioi] at hx hy
  simp only [smul_eq_mul]
  let c := a * x + b * y
  have hc : 0 < c := by
    dsimp [c]
    rcases ha.eq_or_lt with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      simp [← ha0, hb1, hy]
    · exact add_pos_of_pos_of_nonneg (mul_pos ha0 hx) (mul_nonneg hb hy.le)
  have hsum : a * x / c + b * y / c = 1 := by
    rw [← add_div]; exact div_self (ne_of_gt hc)
  have harg : a * x / c * (s / x) + b * y / c * (s / y) = s / c := by
    calc
      _ = (a + b) * s / c := by
        field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hc]

      _ = s / c := by rw [hab, one_mul]
  have h := hf.2 (div_pos hs hx) (div_pos hs hy)
    (div_nonneg (mul_nonneg ha hx.le) hc.le)
    (div_nonneg (mul_nonneg hb hy.le) hc.le) hsum
  simp only [smul_eq_mul, harg] at h
  have hh := mul_le_mul_of_nonneg_left h hc.le
  have hright : c * (a * x / c * f (s / x) + b * y / c * f (s / y)) =
      a * (x * f (s / x)) + b * (y * f (s / y)) := by
    field_simp [ne_of_gt hc]

  rw [hright] at hh
  exact hh
end SimonThreshold
