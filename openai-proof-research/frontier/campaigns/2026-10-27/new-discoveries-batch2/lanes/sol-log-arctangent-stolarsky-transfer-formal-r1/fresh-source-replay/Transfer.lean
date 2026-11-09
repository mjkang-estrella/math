import Stolarsky

set_option autoImplicit false
set_option warningAsError true

namespace LogArctangentSource

/-- The centered pair, scaled by its geometric center, is the original pair. -/
theorem centered_representation {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let t := (Real.log b - Real.log a)/2
    let k := Real.exp ((Real.log a + Real.log b)/2)
    k * Real.exp (-t) = a ∧ k * Real.exp t = b := by
  dsimp
  constructor
  · rw [← Real.exp_add, show (Real.log a + Real.log b)/2 + -((Real.log b - Real.log a)/2) = Real.log a by ring, Real.exp_log ha]
  · rw [← Real.exp_add, show (Real.log a + Real.log b)/2 + (Real.log b - Real.log a)/2 = Real.log b by ring, Real.exp_log hb]

theorem gap_log_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    centeredLogGap ((Real.log b - Real.log a)/2) = Real.log (fixedS a b / mean a b) := by
  let t := (Real.log b - Real.log a)/2
  let k := Real.exp ((Real.log a + Real.log b)/2)
  obtain ⟨hea,heb⟩ := centered_representation ha hb
  change k * Real.exp (-t) = a at hea
  change k * Real.exp t = b at heb
  have hk : 0 < k := Real.exp_pos _
  have hs := fixedS_homogeneous (Real.exp_pos (-t)) (Real.exp_pos t) hk
  have hm := mean_homogeneous (Real.exp_pos (-t)) (Real.exp_pos t) hk
  rw [hea,heb] at hs hm
  rw [Real.log_div (fixedS_pos ha hb).ne' (mean_pos ha hb).ne', hs, hm,
    Real.log_mul hk.ne' (fixedS_pos (Real.exp_pos _) (Real.exp_pos _)).ne',
    Real.log_mul hk.ne' (mean_pos (Real.exp_pos _) (Real.exp_pos _)).ne']
  unfold centeredLogGap
  dsimp [t]
  ring

theorem subinterval_ratio {a b c : ℝ} (hmono : StrictMonoOn centeredLogGap (Set.Ioi 0))
    (ha : 0 < a) (hac : a < c) (hcb : c < b) :
    (mean a b / fixedS a b) * fixedS a c < mean a c ∧
    (mean a b / fixedS a b) * fixedS c b < mean c b := by
  have hc := ha.trans hac
  have hb := hc.trans hcb
  have hla := Real.log_lt_log ha hac
  have hlb := Real.log_lt_log hc hcb
  have hx : 0 < (Real.log c - Real.log a)/2 := by linarith
  have hy : 0 < (Real.log b - Real.log c)/2 := by linarith
  have ht : 0 < (Real.log b - Real.log a)/2 := by linarith
  have hxt : (Real.log c - Real.log a)/2 < (Real.log b - Real.log a)/2 := by linarith
  have hyt : (Real.log b - Real.log c)/2 < (Real.log b - Real.log a)/2 := by linarith
  have hxg := hmono hx ht hxt
  have hyg := hmono hy ht hyt
  rw [gap_log_ratio ha hc, gap_log_ratio ha hb] at hxg
  rw [gap_log_ratio hc hb, gap_log_ratio ha hb] at hyg
  have hxr : fixedS a c / mean a c < fixedS a b / mean a b :=
    (Real.log_lt_log_iff (div_pos (fixedS_pos ha hc) (mean_pos ha hc))
      (div_pos (fixedS_pos ha hb) (mean_pos ha hb))).mp hxg
  have hyr : fixedS c b / mean c b < fixedS a b / mean a b :=
    (Real.log_lt_log_iff (div_pos (fixedS_pos hc hb) (mean_pos hc hb))
      (div_pos (fixedS_pos ha hb) (mean_pos ha hb))).mp hyg
  constructor
  · have h := (div_lt_div_iff₀ (mean_pos ha hc) (mean_pos ha hb)).mp hxr
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (fixedS_pos ha hb)).mpr
    simpa only [mul_comm] using h
  · have h := (div_lt_div_iff₀ (mean_pos hc hb) (mean_pos ha hb)).mp hyr
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (fixedS_pos ha hb)).mpr
    simpa only [mul_comm] using h

theorem transfer_of_stabilization {p q a b : ℝ}
    (hmono : StrictMonoOn centeredLogGap (Set.Ioi 0))
    (hp : p ≠ 0) (hq : q ≠ 0) (ha : 0 < a) (hab : a < b)
    (hstab : powerMean p (fixedS a (powerMean q a b))
      (fixedS (powerMean q a b) b) = fixedS a b) : mean a b < resultant p q a b := by
  have hb := ha.trans hab
  let c := powerMean q a b
  have hc : 0 < c := powerMean_pos ha hb
  obtain ⟨hac,hcb⟩ := powerMean_between hq ha hab
  obtain ⟨hx,hy⟩ := subinterval_ratio hmono ha hac hcb
  have hk : 0 < mean a b / fixedS a b := div_pos (mean_pos ha hb) (fixedS_pos ha hb)
  have h := powerMean_strict_mono hp
    (mul_pos hk (fixedS_pos ha hc)) (mul_pos hk (fixedS_pos hc hb)) hx hy
  rw [powerMean_homogeneous (fixedS_pos ha hc) (fixedS_pos hc hb) hk, hstab] at h
  have he : mean a b / fixedS a b * fixedS a b = mean a b :=
    div_mul_cancel₀ _ (fixedS_pos ha hb).ne'
  rw [he] at h
  exact h

/-- Conditional integration endpoint: the sole analytic premise is strict gap monotonicity. -/
theorem sourceClaim_of_strictMono_gap
    (hmono : StrictMonoOn centeredLogGap (Set.Ioi 0)) : SourceClaim := by
  have hd : d ≠ 0 := (lt_trans (by norm_num) d_bounds.1).ne'
  have hb : beta ≠ 0 := parameters.1.ne'
  have ha : alpha ≠ 0 := (parameters.1.trans parameters.2.1).ne'
  have ordered : ∀ a b : ℝ, 0 < a → a < b →
      mean a b < resultant d beta a b ∧ mean a b < resultant (-d) alpha a b := by
    intro a b hapos hab
    constructor
    · exact transfer_of_stabilization hmono hd hb hapos hab
        (fixedS_stabilization_positive hapos hab)
    · exact transfer_of_stabilization hmono (neg_ne_zero.mpr hd) ha hapos hab
        (fixedS_stabilization_negative hapos hab)
  intro a b hapos hbpos hne
  rcases lt_or_gt_of_ne hne with hab | hab
  · exact ordered a b hapos hab
  · rw [mean_symm a b, resultant_symm _ _ a b, resultant_symm _ _ a b]
    exact ordered b a hbpos hab

end LogArctangentSource
