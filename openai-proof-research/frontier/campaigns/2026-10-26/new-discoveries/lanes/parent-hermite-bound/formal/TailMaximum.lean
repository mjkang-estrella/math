import RootMoments

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

open Polynomial Filter Set
open scoped Topology

theorem polynomial_gaussian_tendsto (p : Polynomial ℝ) :
    Tendsto (fun x : ℝ => p.eval x * Real.exp (-(x ^ 2) / 2)) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    · funext x
      simp only [eval_add]
      ring
    · simp
  | monomial k a =>
    have h := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (show (0 : ℝ) < 1 / 2 by norm_num) (k : ℝ)).mono_left atTop_le_cocompact
    have he : (fun x : ℝ => x ^ k * Real.exp (-(x ^ 2) / 2)) =ᶠ[atTop]
        (fun x : ℝ => |x| ^ (k : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [abs_of_nonneg hx, Real.rpow_natCast]
      congr 2
      ring
    have hm := (h.congr' he.symm).const_mul a
    simpa only [eval_monomial, mul_assoc, mul_zero] using hm

theorem square_le_at_left_of_no_stationary (f g : ℝ → ℝ) (a : ℝ)
    (hd : ∀ x, HasDerivAt f (g x) x)
    (ht : Tendsto f atTop (𝓝 0))
    (hn : ∀ x, a ≤ x → f x ≠ 0 → g x ≠ 0) :
    ∀ x, a ≤ x → f x ^ 2 ≤ f a ^ 2 := by
  intro x hx
  by_contra hle
  have hlt : f a ^ 2 < f x ^ 2 := lt_of_not_ge hle
  have hpos : 0 < f x ^ 2 := lt_of_le_of_lt (sq_nonneg _) hlt
  have ht2 : Tendsto (fun t => f t ^ 2) atTop (𝓝 (0 : ℝ)) := by simpa using ht.pow 2
  have hev : ∀ᶠ R in atTop, f R ^ 2 < f x ^ 2 := by
    exact ht2.eventually (gt_mem_nhds hpos)
  obtain ⟨R, hxR, hR⟩ := ((eventually_gt_atTop x).and hev).exists
  have haR : a ≤ R := hx.trans hxR.le
  have hc : Continuous (fun t => f t ^ 2) :=
    (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).pow 2
  obtain ⟨c, hcmem, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc a R).Nonempty from ⟨a, le_rfl, haR⟩) hc.continuousOn
  have hxc : f x ^ 2 ≤ f c ^ 2 := hmax ⟨hx, hxR.le⟩
  have hac : a < c := by
    apply lt_of_le_of_ne hcmem.1
    intro he
    rw [← he] at hxc
    linarith
  have hcR : c < R := by
    apply lt_of_le_of_ne hcmem.2
    intro he
    rw [he] at hxc
    linarith
  have hcne : f c ≠ 0 := by
    intro he
    rw [he] at hxc
    nlinarith
  have hzero := (hmax.isLocalMax (Icc_mem_nhds hac hcR)).hasDerivAt_eq_zero
    ((hd c).pow 2)
  have hgne := hn c hac.le hcne
  norm_num at hzero
  exact hzero.elim hcne hgne

theorem sourceCutoff_pos (n : ℕ) (hn : 1 ≤ n) : 0 < sourceCutoff n := by
  have hE : 3 ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast (show 3 ≤ 2 * n + 1 by omega)
  unfold sourceCutoff
  apply mul_pos (Real.sqrt_pos.mpr (by linarith))
  apply sub_pos.mpr
  apply (div_lt_one (by linarith)).mpr
  linarith [Real.pi_lt_four]

theorem sourceCutoff_sq (n : ℕ) :
    sourceCutoff n ^ 2 = 2 * (n : ℝ) + 1 - Real.pi +
      Real.pi ^ 2 / (4 * (2 * (n : ℝ) + 1)) := by
  have hE : 0 < 2 * (n : ℝ) + 1 := by positivity
  unfold sourceCutoff
  rw [mul_pow, Real.sq_sqrt hE.le]
  field_simp
  ring

theorem sourceCutoff_sq_lt (n : ℕ) (hn : 1 ≤ n) :
    sourceCutoff n ^ 2 < 2 * (n : ℝ) + 1 := by
  have hE : 3 ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast (show 3 ≤ 2 * n + 1 by omega)
  rw [sourceCutoff_sq]
  have hp : Real.pi ^ 2 / (4 * (2 * (n : ℝ) + 1)) < Real.pi := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hlt : Real.pi < 4 * (2 * (n : ℝ) + 1) := by linarith [Real.pi_lt_four]
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hlt)]
  linarith

theorem source_tail_square (n : ℕ) (hn : 3 ≤ n) (x : ℝ)
    (hx : sourceCutoff n ≤ x) :
    weightedHermite n x ^ 2 ≤ weightedHermite n (sourceCutoff n) ^ 2 := by
  apply square_le_at_left_of_no_stationary (weightedHermite n) (weightedSlope n)
    (sourceCutoff n) (weightedHermite_hasDerivAt n)
    (polynomial_gaussian_tendsto (hermitePoly n)) ?_ x hx
  intro t ht hy hs
  apply no_stationary_peak_beyond_square_cutoff n t hn ?_ hy hs
  rw [← sourceCutoff_sq]
  have ha := sourceCutoff_pos n (by omega)
  nlinarith

theorem source_tail_abs (n : ℕ) (hn : 3 ≤ n) (x : ℝ)
    (hx : sourceCutoff n ≤ x) :
    |weightedHermite n x| ≤ |weightedHermite n (sourceCutoff n)| := by
  exact (sq_le_sq).mp (source_tail_square n hn x hx)

end HermiteEnvelope
