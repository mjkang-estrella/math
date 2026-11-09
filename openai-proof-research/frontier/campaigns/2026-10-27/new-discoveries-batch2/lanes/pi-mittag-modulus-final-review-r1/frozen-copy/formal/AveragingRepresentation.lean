import BetaAverages

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Filter

namespace MittagModulus

noncomputable def halfTerm (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  x ^ ((n : ℝ) / 2) • (z ^ n / (Real.Gamma (1 + (n : ℝ) / 2) : ℂ))

theorem halfTerm_continuous (z : ℂ) (n : ℕ) : Continuous (halfTerm z n) := by
  exact (Real.continuous_rpow_const (by positivity : 0 ≤ (n : ℝ) / 2)).smul continuous_const

theorem halfTerm_eq_series (z : ℂ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    halfTerm z n x = (z * (Real.sqrt x : ℂ)) ^ n /
      (Real.Gamma ((1 / 2 : ℝ) * n + 1) : ℂ) := by
  unfold halfTerm
  rw [Real.rpow_div_two_eq_sqrt _ hx, Real.rpow_natCast, Complex.real_smul,
    Complex.ofReal_pow, mul_pow]
  rw [show 1 + (n : ℝ) / 2 = (1 / 2 : ℝ) * n + 1 by ring]
  ring

theorem hasSum_halfTerm (z : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => halfTerm z n x)
      (mittagLeffler (1 / 2) 1 (z * (Real.sqrt x : ℂ))) := by
  simpa only [halfTerm_eq_series z _ hx] using
    (hasSum_mittagLeffler (by norm_num : (0 : ℝ) < 1 / 2) zero_lt_one
      (z * (Real.sqrt x : ℂ)))

theorem halfTerm_norm_le (z : ℂ) (n : ℕ) {C x : ℝ} (hx : x ∈ Set.Icc 0 C) :
    ‖halfTerm z n x‖ ≤ (‖z‖ * Real.sqrt C) ^ n /
      Real.Gamma ((1 / 2 : ℝ) * n + 1) := by
  rw [halfTerm_eq_series z n hx.1, norm_div, norm_pow, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.Gamma_pos_of_pos (by positivity))]
  gcongr
  exact hx.2

theorem finiteBetaAverage_halfTerm (β : ℝ) (m : ℕ) (z : ℂ) (n : ℕ) {x : ℝ}
    (hx : 0 ≤ x) :
    finiteBetaAverage β m (halfTerm z n) x =
      (x ^ ((n : ℝ) / 2) * ∏ k ∈ Finset.range m,
        ((1 + β * ((n : ℝ) / 2) + (k : ℝ)) / (1 + (n : ℝ) / 2 + (k : ℝ)))) •
      (z ^ n / (Real.Gamma (1 + (n : ℝ) / 2) : ℂ)) := by
  unfold halfTerm
  rw [finiteBetaAverage_smul_const]
  dsimp only
  rw [finiteBetaAverage_rpow (by positivity) m hx]

theorem halfTerm_partial_norm_le (z : ℂ) (m : ℕ) {C x : ℝ} (hx : x ∈ Set.Icc 0 C) :
    ‖∑ n ∈ Finset.range m, halfTerm z n x‖ ≤
      ∑' n : ℕ, (‖z‖ * Real.sqrt C) ^ n / Real.Gamma ((1 / 2 : ℝ) * n + 1) := by
  have hs := mittag_real_majorant_summable (by norm_num : (0 : ℝ) < 1 / 2)
    zero_lt_one (mul_nonneg (norm_nonneg z) (Real.sqrt_nonneg C))
  calc
    ‖∑ n ∈ Finset.range m, halfTerm z n x‖ ≤ ∑ n ∈ Finset.range m, ‖halfTerm z n x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range m,
        (‖z‖ * Real.sqrt C) ^ n / Real.Gamma ((1 / 2 : ℝ) * n + 1) :=
      Finset.sum_le_sum (fun n _ => halfTerm_norm_le z n hx)
    _ ≤ ∑' n : ℕ, (‖z‖ * Real.sqrt C) ^ n / Real.Gamma ((1 / 2 : ℝ) * n + 1) :=
      hs.sum_le_tsum (Finset.range m) (fun _ _ => by positivity)

theorem finiteBetaAverage_halfSum_tendsto {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (m : ℕ) (z : ℂ) {x : ℝ} (hx : x ∈ Set.Icc 0 C) :
    Tendsto (fun N => finiteBetaAverage β m
      (fun y => ∑ n ∈ Finset.range N, halfTerm z n y) x) atTop
      (nhds (finiteBetaAverage β m
        (fun y => mittagLeffler (1 / 2) 1 (z * (Real.sqrt y : ℂ))) x)) := by
  apply finiteBetaAverage_tendsto hβ hβ1 m
    (fun N => continuous_finsetSum _ (fun n _ => halfTerm_continuous z n))
    (fun N y hy => halfTerm_partial_norm_le z N hy)
    (fun y hy => (hasSum_halfTerm z hy.1).summable.hasSum_iff_tendsto_nat.mp
      (hasSum_halfTerm z hy.1)) x hx

theorem finiteBetaAverage_halfTerm_at_scale (a : ℝ) (N n : ℕ) (z : ℂ) :
    finiteBetaAverage (2 * a) (N + 2) (halfTerm z n)
      (((N : ℝ) + 1) ^ (1 - 2 * a)) = (approxCoeff a n N : ℂ) * z ^ n := by
  unfold halfTerm
  rw [finiteBetaAverage_smul_const]
  change finiteBetaAverage (2 * a) (N + 2) (fun y : ℝ => y ^ ((n : ℝ) / 2))
    (((N : ℝ) + 1) ^ (1 - 2 * a)) • _ = _
  rw [← momentApprox_eq_finiteBetaAverage (by positivity)]
  simp only [approxCoeff, Complex.ofReal_div, Complex.real_smul]
  ring

theorem approxTransform_eq_finiteBetaAverage {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (N : ℕ) (z : ℂ) :
    approxTransform a N z =
      finiteBetaAverage (2 * a) (N + 2)
        (fun y => mittagLeffler (1 / 2) 1 (z * (Real.sqrt y : ℂ)))
        (((N : ℝ) + 1) ^ (1 - 2 * a)) := by
  have hpos : 0 ≤ ((N : ℝ) + 1) ^ (1 - 2 * a) := Real.rpow_nonneg (by positivity) _
  have hlim := finiteBetaAverage_halfSum_tendsto (by positivity : 0 ≤ 2 * a)
    (by linarith : 2 * a ≤ 1) (N + 2) z ⟨hpos, le_rfl⟩
  have he : (fun M => finiteBetaAverage (2 * a) (N + 2)
      (fun y => ∑ n ∈ Finset.range M, halfTerm z n y)
        (((N : ℝ) + 1) ^ (1 - 2 * a))) =
      (fun M => ∑ n ∈ Finset.range M, (approxCoeff a n N : ℂ) * z ^ n) := by
    funext M
    rw [finiteBetaAverage_sum (2 * a) (N + 2) (Finset.range M)
      (fun n _ => halfTerm_continuous z n)]
    simp only [finiteBetaAverage_halfTerm_at_scale]
  rw [he] at hlim
  have hsource : Tendsto (fun M => ∑ n ∈ Finset.range M, (approxCoeff a n N : ℂ) * z ^ n)
      atTop (nhds (approxTransform a N z)) :=
    (approxTransform_summable ha ha2 N z).hasSum_iff_tendsto_nat.mp
      (approxTransform_summable ha ha2 N z).hasSum
  exact tendsto_nhds_unique hsource hlim

end MittagModulus
