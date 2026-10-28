import GammaDefs

set_option autoImplicit false
set_option warningAsError true

/-!
# Closed series-level analysis of the literal defect series

`seriesDefect x s = ∑' m, seriesTerm x s m`, where `seriesTerm x s m =
-log (1 - ((s+m)/x)⁻¹²)`.  This module analyses the *literal* series without
any Gamma-function identification.  Everything here is proved by actual
analysis of the series:

* `summable_seriesTerm` — convergence for every `s > x`;
* `continuousOn_seriesDefect` — continuity on `Ioi x`;
* `strictAnti_seriesDefect` — strict antitonicity on `Ioi x`;
* `seriesDefect_tendsto_zero` — the sum tends to `0` as `s → +∞`;
* `seriesDefect_tendsto_atTop` — the sum diverges to `+∞` as `s → x⁺`;
* `existsUnique_seriesDefect` — for every `x > 0`, `d > 0` a unique `y > 0`
  with `seriesDefect x (x + y) = d`.

Key uniform bound (valid for all `s > x`, `m ≥ 1`):
`0 ≤ seriesTerm x s m ≤ x²/((s+m)² - x²) ≤ x²/m²`,
because `log y ≤ y - 1` gives `-log(1-t) ≤ t/(1-t)` and
`(s+m)² - x² = (s+m-x)(s+m+x) > m²`.
-/

noncomputable section
open Set Filter Topology
namespace GammaLevel

/-- The literal defect series sum. -/
def seriesDefect (x s : ℝ) : ℝ := ∑' m, seriesTerm x s m

/-- The tail of the defect series (all terms from index 1 on). -/
def seriesDefectTail (x s : ℝ) : ℝ := ∑' n, seriesTerm x s (n + 1)

/-! ### Elementary term estimates -/

/-- For `0 ≤ t < 1`, `-log(1-t) ≤ t/(1-t)`. -/
private theorem neg_log_sub_le {t : ℝ} (_h0 : 0 ≤ t) (h1 : t < 1) :
    -Real.log (1 - t) ≤ t / (1 - t) := by
  have hy : 0 < (1 - t)⁻¹ := inv_pos.mpr (by linarith)
  have h := Real.log_le_sub_one_of_pos hy
  rw [Real.log_inv] at h
  have hz : 1 - t ≠ 0 := by linarith
  have hr : (1 - t)⁻¹ - 1 = t / (1 - t) := by
    rw [eq_div_iff hz, sub_mul, inv_mul_cancel₀ hz]
    ring
  linarith

/-- The term of the defect series is nonnegative whenever `s > x`. -/
theorem level_seriesTerm_nonneg {x s : ℝ} (hx : 0 < x) (hs : x < s) (m : ℕ) :
    0 ≤ seriesTerm x s m := by
  have hsm : 0 < s + m := by linarith
  have hu1 : 0 < (s + m) / x := div_pos hsm hx
  have hu2 : 1 < (s + m) / x := by
    rw [one_lt_div₀ hx]; linarith
  have ht1 : ((s + m) / x)⁻¹ < 1 := (inv_lt_one₀ hu1).mpr hu2
  have ht0 : 0 < ((s + m) / x)⁻¹ := inv_pos.mpr hu1
  have ht2 : ((s + m) / x)⁻¹ ^ 2 < 1 := by
    have key : (0 : ℝ) < (1 - ((s + m) / x)⁻¹) * (1 + ((s + m) / x)⁻¹) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [key]
  have hsq : ((s + m) / x)⁻¹ ^ 2 ≤ 1 := le_of_lt ht2
  have hpos : 0 < (1 : ℝ) - ((s + m) / x)⁻¹ ^ 2 := by linarith
  have hle := Real.log_nonpos (le_of_lt hpos)
    (show (1 : ℝ) - ((s + m) / x)⁻¹ ^ 2 ≤ 1 by
      linarith [sq_nonneg ((s + m) / x)⁻¹])
  show 0 ≤ -Real.log (1 - ((s + m) / x)⁻¹ ^ 2)
  exact neg_nonneg.mpr hle

/-- Key uniform bound: for `m ≥ 1` and all `s > x`, `seriesTerm x s m ≤ x²/m²`. -/
theorem seriesTerm_le_inv_sq {x s : ℝ} (hx : 0 < x) (hs : x < s) {m : ℕ} (hm : 0 < m) :
    seriesTerm x s m ≤ x ^ 2 / ((m : ℝ) ^ 2) := by
  have hsm : 0 < s + m := by linarith
  have hsmx : x < s + m := by linarith
  -- ((s+m)/x)⁻¹² = x²/(s+m)²
  have hinv : ((s + m) / x)⁻¹ ^ 2 = x ^ 2 / (s + m) ^ 2 := by
    rw [inv_div, div_pow]
  -- (s+m)² > x²
  have hsq1 : x ^ 2 < (s + m) ^ 2 := by
    refine (sq_lt_sq).mpr ?_
    rw [abs_of_pos (show 0 < (x : ℝ) from hx), abs_of_pos hsm]
    exact hsmx
  have hD : 0 < (s + m) ^ 2 - x ^ 2 := by linarith
  -- m² ≤ (s+m)² - x²
  have hm2 : (m : ℝ) ^ 2 ≤ (s + m) ^ 2 - x ^ 2 := by
    have h1 : (0 : ℝ) < s + m - x - m := by linarith
    have h2 : (0 : ℝ) < s + m + x - m := by linarith
    have h3 : (0 : ℝ) < (s + m - x - m) * (s + m + x - m) := mul_pos h1 h2
    have h4 : ((s + m) - x) * ((s + m) + x) > (m : ℝ) ^ 2 := by
      nlinarith [h3, h1, h2, (show (0 : ℝ) ≤ (m : ℝ) by exact_mod_cast hm.le)]
    have hrw : ((s + m) - x) * ((s + m) + x) = (s + m) ^ 2 - x ^ 2 := by ring
    linarith [h4, hrw]
  set t : ℝ := x ^ 2 / (s + m) ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := by
    rw [ht, div_lt_one₀ (sq_pos_of_pos hsm)]
    exact hsq1
  have hterm : seriesTerm x s m = -Real.log (1 - t) := by
    show -Real.log (1 - ((s + m) / x)⁻¹ ^ 2) = -Real.log (1 - t)
    rw [hinv]
  have h1 := neg_log_sub_le ht0 ht1
  have h2 : t / (1 - t) = x ^ 2 / ((s + m) ^ 2 - x ^ 2) := by
    rw [ht]; field_simp
  rw [h2] at h1
  -- x²/((s+m)²-x²) ≤ x²/m²
  have h3 : x ^ 2 / ((s + m) ^ 2 - x ^ 2) ≤ x ^ 2 / (m : ℝ) ^ 2 := by
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    rw [div_le_iff₀ hD, div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hmR)]
    exact mul_le_mul_of_nonneg_left hm2 (sq_nonneg x)
  rw [hterm]
  linarith

/-! ### Summability -/

/-- The majorant series `∑ x²/(n+1)²` is summable. -/
private theorem summable_u (x : ℝ) :
    Summable (fun n : ℕ => x ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hpow : Summable (fun n : ℕ => (((n : ℝ) ^ 2)⁻¹)) :=
    (Real.summable_nat_pow_inv (p := 2)).mpr one_lt_two
  have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1 (f := fun n : ℕ => (((n : ℝ) ^ 2)⁻¹))).mpr hpow
  have hsm := hshift.smul_const (x ^ 2)
  have hcongr : ∀ n : ℕ, (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ • x ^ 2
      = x ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n
    rw [smul_eq_mul, div_eq_inv_mul]
  exact hsm.congr hcongr

/-- The defect series converges for every `s > x`. -/
theorem summable_seriesTerm {x s : ℝ} (hx : 0 < x) (hs : x < s) :
    Summable (seriesTerm x s) := by
  have htail : Summable (fun n : ℕ => seriesTerm x s (n + 1)) :=
    Summable.of_nonneg_of_le (fun n => level_seriesTerm_nonneg hx hs (n + 1))
      (fun n => seriesTerm_le_inv_sq hx hs (show 0 < n + 1 by omega))
      (summable_u x)
  exact (summable_nat_add_iff 1).mp htail

/-- Split of the defect series into its 0-term and its tail. -/
theorem seriesDefect_eq {x s : ℝ} (hx : 0 < x) (hs : x < s) :
    seriesDefect x s = seriesTerm x s 0 + seriesDefectTail x s := by
  show ∑' m, seriesTerm x s m = seriesTerm x s 0 + ∑' n, seriesTerm x s (n + 1)
  exact Summable.tsum_eq_zero_add (summable_seriesTerm hx hs)

/-- The defect sum dominates its 0-term on `Ioi x`. -/
theorem seriesDefect_ge_zeroTerm {x s : ℝ} (hx : 0 < x) (hs : x < s) :
    seriesTerm x s 0 ≤ seriesDefect x s := by
  have h := summable_seriesTerm hx hs
  exact Summable.le_tsum h 0 (fun j _ => level_seriesTerm_nonneg hx hs j)

/-! ### The profile is continuous and strictly antitone on `(1, ∞)` -/

theorem profile_continuousOn : ContinuousOn profile (Ioi 1) := by
  have hinv : ContinuousOn (fun u : ℝ => (u : ℝ)⁻¹) (Ioi 1) :=
    (continuousOn_inv₀ (G₀ := ℝ)).comp continuousOn_id
      (fun u hu => by
        rw [mem_compl_singleton_iff]
        exact ne_of_gt (lt_trans zero_lt_one (mem_Ioi.mp hu)))
  have hsq2 : ContinuousOn (fun u : ℝ => (u : ℝ)⁻¹ ^ 2) (Ioi 1) :=
    (hinv.mul hinv).congr fun u _ => sq ((u : ℝ)⁻¹)
  have hmaps : ∀ u ∈ Ioi 1, (1 : ℝ) - u⁻¹ ^ 2 ≠ 0 := by
    intro u hu
    have hu1 : 0 < u⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hu)
    have hu2 : u⁻¹ < 1 := (inv_lt_one₀ (lt_trans zero_lt_one hu)).mpr hu
    exact ne_of_gt (by nlinarith [hu1, hu2])
  have hlog : ContinuousOn (fun u : ℝ => Real.log ((1 : ℝ) - u⁻¹ ^ 2)) (Ioi 1) :=
    ContinuousOn.log (ContinuousOn.sub
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Ioi 1)) hsq2) hmaps
  exact hlog.neg

/-- The profile is strictly antitone on `(1, ∞)`. -/
theorem profile_strictAnti : StrictAntiOn profile (Ioi 1) := by
  intro a ha b hb hab
  have hapos : 0 < (a : ℝ) := lt_trans zero_lt_one ha
  have hbpos : 0 < (b : ℝ) := lt_trans zero_lt_one hb
  have hinv : b⁻¹ < a⁻¹ := (inv_lt_inv₀ hbpos hapos).mpr hab
  have hsq : b⁻¹ ^ 2 < a⁻¹ ^ 2 :=
    pow_lt_pow_left₀ hinv (le_of_lt (inv_pos.mpr hbpos)) two_ne_zero
  have ha1 : a⁻¹ < 1 := (inv_lt_one₀ hapos).mpr ha
  have hlt1 : 0 < (1 : ℝ) - a⁻¹ ^ 2 := by
    have key : (0 : ℝ) < (1 - a⁻¹) * (1 + a⁻¹) :=
      mul_pos (by linarith) (by linarith [inv_pos.mpr hapos])
    nlinarith [key]
  have hlt : 1 - a⁻¹ ^ 2 < 1 - b⁻¹ ^ 2 := by linarith
  have hlog := Real.log_lt_log hlt1 hlt
  show -Real.log (1 - b⁻¹ ^ 2) < -Real.log (1 - a⁻¹ ^ 2)
  linarith

/-- Each term of the series tends to `0` as `s → +∞`. -/
theorem seriesTerm_tendsto_zero {x : ℝ} (hx : 0 < x) (m : ℕ) :
    Tendsto (fun s => seriesTerm x s m) atTop (𝓝 0) := by
  have haff : Tendsto (fun s : ℝ => (s + (m : ℝ)) / x) atTop atTop := by
    have h1 : Tendsto (fun s : ℝ => s) atTop atTop := tendsto_id
    have h2 := tendsto_atTop_add_const_right atTop ((m : ℝ)) h1
    have h3 : Tendsto (fun s : ℝ => (s + (m : ℝ)) * x⁻¹) atTop atTop :=
      Tendsto.atTop_mul_pos (inv_pos.mpr hx) h2 tendsto_const_nhds
    have hrw : (fun s : ℝ => (s + (m : ℝ)) / x) = fun s : ℝ => (s + (m : ℝ)) * x⁻¹ := by
      funext s; rw [div_eq_inv_mul]; ring
    rw [hrw]; exact h3
  have hprof : Tendsto (fun u : ℝ => -Real.log (1 - u⁻¹ ^ 2)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun u : ℝ => (u : ℝ)⁻¹ ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2
    have h1 : Tendsto (fun u : ℝ => (1 : ℝ) - u⁻¹ ^ 2) atTop (𝓝 1) := by
      have hsub := Tendsto.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)) h2
      simpa using hsub
    have h3 : Tendsto (fun u : ℝ => Real.log (1 - u⁻¹ ^ 2)) atTop (𝓝 0) := by
      have hlog := Filter.Tendsto.log h1 one_ne_zero
      simpa using hlog
    simpa using h3.neg
  exact hprof.comp haff

/-! ### Continuity of the defect sum -/

/-- Continuity of `s ↦ profile ((s + a)/x)` on `Ioi x` for any natural shift `a`. -/
private theorem continuousOn_profile_shift (x : ℝ) (hx : 0 < x) (a : ℕ) :
    ContinuousOn (fun s : ℝ => profile ((s + a) / x)) (Ioi x) := by
  have haff : Continuous (fun s : ℝ => (s + (a : ℝ)) / x) :=
    (Continuous.add continuous_id continuous_const : Continuous (fun s : ℝ => s + (a : ℝ))) |>.div_const x
  have hmaps : MapsTo (fun s : ℝ => (s + (a : ℝ)) / x) (Ioi x) (Ioi 1) := by
    intro s hs
    rw [mem_Ioi] at hs ⊢
    refine one_lt_div₀ hx |>.mpr ?_
    linarith [Nat.cast_nonneg (α := ℝ) a]
  have key : ContinuousOn (profile ∘ (fun s : ℝ => (s + (a : ℝ)) / x)) (Ioi x) :=
    ContinuousOn.comp profile_continuousOn haff.continuousOn hmaps
  exact key

theorem continuousOn_seriesDefectTail (x : ℝ) (hx : 0 < x) :
    ContinuousOn (seriesDefectTail x) (Ioi x) := by
  refine continuousOn_tsum (f := fun (n : ℕ) (s : ℝ) => seriesTerm x s (n + 1))
    (u := fun n : ℕ => x ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2) (s := Ioi x)
    (fun n => continuousOn_profile_shift x hx (n + 1)) (summable_u x) ?_
  intro n s hsn
  have hs : x < s := hsn
  calc ‖seriesTerm x s (n + 1)‖ = seriesTerm x s (n + 1) :=
        Real.norm_of_nonneg (level_seriesTerm_nonneg hx hs (n + 1))
    _ ≤ x ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 := seriesTerm_le_inv_sq hx hs (by omega)
    _ = x ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 := rfl

theorem continuousOn_seriesDefect (x : ℝ) (hx : 0 < x) :
    ContinuousOn (seriesDefect x) (Ioi x) := by
  have h0 : ContinuousOn (fun s : ℝ => seriesTerm x s 0) (Ioi x) := by
    have h : (fun s : ℝ => seriesTerm x s 0) = fun s : ℝ => profile ((s + (0 : ℕ)) / x) :=
      rfl
    rw [h]
    exact continuousOn_profile_shift x hx 0
  refine (h0.add (continuousOn_seriesDefectTail x hx)).congr fun s hs => ?_
  exact seriesDefect_eq hx (mem_Ioi.mp hs)

/-! ### Limit at infinity -/

/-- The tail of the defect series tends to `0` as `s → +∞`. -/
theorem seriesDefectTail_tendsto_zero (x : ℝ) (hx : 0 < x) :
    Tendsto (seriesDefectTail x) atTop (𝓝 0) := by
  have hdom : ∀ᶠ n in atTop, ∀ s ∈ (Ioi x), ‖seriesTerm x s (n + 1)‖
      ≤ x ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    filter_upwards with n s hs
    have hsx : x < s := hs
    calc ‖seriesTerm x s (n + 1)‖ = seriesTerm x s (n + 1) :=
          Real.norm_of_nonneg (level_seriesTerm_nonneg hx hsx (n + 1))
      _ ≤ x ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 := seriesTerm_le_inv_sq hx hsx (by omega)
  have hunif := tendstoUniformlyOn_tsum_nat_eventually (summable_u x) hdom
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  -- uniform approximation of the tail by its partial sums
  obtain ⟨N, hN⟩ := (eventually_atTop).mp (hunif (ε / 2) (by linarith))
  -- the fixed partial sum tends to 0 as s → +∞
  have hpt : Tendsto (fun s : ℝ => ∑ n ∈ Finset.range N, seriesTerm x s (n + 1)) atTop
      (𝓝 0) := by
    have hsum := tendsto_finsetSum (Finset.range N)
      (fun m _ => seriesTerm_tendsto_zero hx (m + 1))
    simpa using hsum
  obtain ⟨B, hB⟩ := (eventually_atTop).mp
    (hpt.eventually (Metric.ball_mem_nhds (x := (0 : ℝ)) (ε := ε / 2) (by linarith)))
  refine Filter.eventually_atTop.2 ⟨max B (x + 1), fun s hs => ?_⟩
  have hsB : B ≤ s := le_trans (le_max_left B (x + 1)) hs
  have hsx : x < s := by
    have h1 : x + 1 ≤ s := le_trans (le_max_right B (x + 1)) hs
    linarith
  have e1 : dist (seriesDefectTail x s) (∑ m ∈ Finset.range N, seriesTerm x s (m + 1))
      < ε / 2 := hN N (le_refl N) s (mem_Ioi.mpr hsx)
  have e2 : dist (∑ m ∈ Finset.range N, seriesTerm x s (m + 1)) 0 < ε / 2 := hB s hsB
  have h1 : |seriesDefectTail x s - (∑ m ∈ Finset.range N, seriesTerm x s (m + 1))|
      < ε / 2 := by
    rwa [Real.dist_eq] at e1
  have h2 : |(∑ m ∈ Finset.range N, seriesTerm x s (m + 1)) - 0| < ε / 2 := by
    rwa [Real.dist_eq] at e2
  have e3 : |seriesDefectTail x s - 0| < ε := by
    have hkey : |seriesDefectTail x s - 0|
        = |(seriesDefectTail x s - (∑ m ∈ Finset.range N, seriesTerm x s (m + 1)))
            + ((∑ m ∈ Finset.range N, seriesTerm x s (m + 1)) - 0)| := by
      congr 1; ring
    rw [hkey]
    have habs := abs_add_le
      (seriesDefectTail x s - (∑ m ∈ Finset.range N, seriesTerm x s (m + 1)))
      ((∑ m ∈ Finset.range N, seriesTerm x s (m + 1)) - 0)
    linarith
  simpa using e3

/-- The defect sum tends to `0` as `s → +∞`. -/
theorem seriesDefect_tendsto_zero (x : ℝ) (hx : 0 < x) :
    Tendsto (seriesDefect x) atTop (𝓝 0) := by
  refine Tendsto.congr'
    (f₁ := fun s : ℝ => seriesTerm x s 0 + seriesDefectTail x s) ?_ ?_
  · filter_upwards [(eventually_ge_atTop (x + 1))] with s hs
    exact (seriesDefect_eq hx (by linarith)).symm
  · have hadd := (seriesTerm_tendsto_zero hx 0).add (seriesDefectTail_tendsto_zero x hx)
    rwa [add_zero] at hadd

/-! ### Divergence at the boundary -/

/-- Core boundary estimate: if `x < s ≤ x/√(1-e^{-M})` then `M ≤ seriesTerm x s 0`. -/
theorem seriesTerm_zero_ge {x : ℝ} (hx : 0 < x) {M : ℝ} (hM : 0 < M) {s : ℝ}
    (hs1 : x < s) (hs2 : s ≤ x / Real.sqrt (1 - Real.exp (-M))) :
    M ≤ seriesTerm x s 0 := by
  have hexp1 : 0 < Real.exp (-M) := Real.exp_pos _
  have hexp2 : Real.exp (-M) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hM)
  have hA0 : 0 < 1 - Real.exp (-M) := by linarith
  have hs0 : 0 < s := lt_trans hx hs1
  have hc : 0 < Real.sqrt (1 - Real.exp (-M)) := Real.sqrt_pos.mpr (by linarith)
  have h1 : s * Real.sqrt (1 - Real.exp (-M)) ≤ x := by
    have hkey := mul_le_mul_of_nonneg_right hs2 hc.le
    rwa [div_mul_cancel₀ x (ne_of_gt hc)] at hkey
  have h2 : (1 : ℝ) - Real.exp (-M) ≤ x ^ 2 / s ^ 2 := by
    have h3 : Real.sqrt (1 - Real.exp (-M)) ≤ x / s :=
      (le_div_iff₀ hs0).mpr (by rw [mul_comm]; exact h1)
    have h4 : (Real.sqrt (1 - Real.exp (-M))) ^ 2 ≤ (x / s) ^ 2 := by
      refine sq_le_sq' ?_ h3
      have hb : 0 < x / s := div_pos hx hs0
      linarith
    have h5 : (Real.sqrt (1 - Real.exp (-M))) ^ 2 = 1 - Real.exp (-M) :=
      Real.sq_sqrt (le_of_lt hA0)
    have h6 : (x / s) ^ 2 = x ^ 2 / s ^ 2 := by rw [div_pow]
    rw [← h5, ← h6]
    exact h4
  have h3 : (1 : ℝ) - x ^ 2 / s ^ 2 ≤ Real.exp (-M) := by linarith
  have hlt : 0 < (1 : ℝ) - x ^ 2 / s ^ 2 := by
    have hsq2 : x ^ 2 < s ^ 2 := by
      refine (sq_lt_sq).mpr ?_
      rw [abs_of_pos (show 0 < (x : ℝ) from hx), abs_of_pos hs0]
      exact hs1
    have := div_lt_one₀ (sq_pos_of_pos hs0) |>.mpr hsq2
    linarith
  have hlog := Real.log_le_log hlt h3
  rw [Real.log_exp] at hlog
  have hterm : seriesTerm x s 0 = -Real.log ((1 : ℝ) - x ^ 2 / s ^ 2) := by
    have hinv : ((s + (0 : ℕ)) / x)⁻¹ ^ 2 = x ^ 2 / s ^ 2 := by
      have hz : ((s + (0 : ℕ)) : ℝ) = s := by simp
      rw [hz, inv_div, div_pow]
    show -Real.log (1 - ((s + (0 : ℕ)) / x)⁻¹ ^ 2) = -Real.log ((1 : ℝ) - x ^ 2 / s ^ 2)
    rw [hinv]
  rw [hterm]
  linarith

/-- The defect sum diverges to `+∞` as `s → x⁺`. -/
theorem seriesDefect_tendsto_atTop (x : ℝ) (hx : 0 < x) :
    Tendsto (seriesDefect x) (𝓝[Ioi x] x) atTop := by
  refine tendsto_atTop.mpr fun M => ?_
  by_cases hM : 0 < M
  · set B : ℝ := x / Real.sqrt (1 - Real.exp (-M)) with hBdef
    have hexp1 : 0 < Real.exp (-M) := Real.exp_pos _
    have hexp2 : Real.exp (-M) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hM)
    have hA0 : 0 < 1 - Real.exp (-M) := by linarith
    have hA1 : 1 - Real.exp (-M) < 1 := by linarith
    have hsqrt : Real.sqrt (1 - Real.exp (-M)) < 1 := by
      have hkey := Real.sqrt_lt_sqrt (le_of_lt hA0) hA1
      rwa [Real.sqrt_one] at hkey
    have hxB : x < B := by
      rw [hBdef, lt_div_iff₀ (Real.sqrt_pos.mpr hA0)]
      have := mul_lt_mul_of_pos_left hsqrt hx
      rw [mul_one] at this
      linarith
    have hsub : (Ioo (x - 1) B) ∩ (Ioi x) ⊆ {s : ℝ | M ≤ seriesDefect x s} := by
      rintro s ⟨⟨_, hsB⟩, hsx⟩
      exact le_trans (seriesTerm_zero_ge hx hM hsx (le_of_lt hsB))
        (seriesDefect_ge_zeroTerm hx hsx)
    exact mem_nhdsWithin.mpr ⟨Ioo (x - 1) B, isOpen_Ioo, ⟨by linarith, hxB⟩, hsub⟩
  · push Not at hM
    have h0le : ∀ s ∈ (Ioi x), M ≤ seriesDefect x s := by
      intro s hsin
      have hg : 0 ≤ seriesDefect x s :=
        tsum_nonneg (fun m => level_seriesTerm_nonneg hx (mem_Ioi.mp hsin) m)
      linarith
    exact mem_nhdsWithin.mpr ⟨Ioo (x - 1) (x + 1), isOpen_Ioo, ⟨by linarith, by linarith⟩,
      fun s hsin => h0le s hsin.2⟩

/-! ### Existence and uniqueness of the level -/

/-- Existence of a level point: for `d > 0` there is `s > x` with `seriesDefect x s = d`. -/
theorem exists_seriesDefect (x : ℝ) (hx : 0 < x) {d : ℝ} (hd : 0 < d) :
    ∃ s : ℝ, x < s ∧ seriesDefect x s = d := by
  -- a point where the sum exceeds d
  obtain ⟨a, ha1, ha2⟩ : ∃ a, x < a ∧ d + 1 ≤ seriesDefect x a := by
    have hexp1 : 0 < Real.exp (-(d + 1)) := Real.exp_pos _
    have hexp2 : Real.exp (-(d + 1)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hA0 : 0 < 1 - Real.exp (-(d + 1)) := by linarith
    have hA1 : 1 - Real.exp (-(d + 1)) < 1 := by linarith
    have hsqrt : Real.sqrt (1 - Real.exp (-(d + 1))) < 1 := by
      have hkey := Real.sqrt_lt_sqrt (le_of_lt hA0) hA1
      rwa [Real.sqrt_one] at hkey
    have hgt : x < x / Real.sqrt (1 - Real.exp (-(d + 1))) := by
      rw [lt_div_iff₀ (Real.sqrt_pos.mpr hA0)]
      have := mul_lt_mul_of_pos_left hsqrt hx
      rw [mul_one] at this
      linarith
    refine ⟨(x + x / Real.sqrt (1 - Real.exp (-(d + 1)))) / 2, by linarith, ?_⟩
    have hs1 : x < (x + x / Real.sqrt (1 - Real.exp (-(d + 1)))) / 2 := by linarith
    have hs2 : (x + x / Real.sqrt (1 - Real.exp (-(d + 1)))) / 2
        ≤ x / Real.sqrt (1 - Real.exp (-(d + 1))) := by linarith
    calc d + 1 ≤ seriesTerm x _ 0 := seriesTerm_zero_ge hx (by linarith) hs1 hs2
      _ ≤ seriesDefect x _ := seriesDefect_ge_zeroTerm hx hs1
  -- a point where the sum is below d
  obtain ⟨b₀, hb₀⟩ := (eventually_atTop).mp
    ((seriesDefect_tendsto_zero x hx).eventually (Iio_mem_nhds hd))
  have hab : a ≤ max b₀ (a + 1) := by
    refine le_trans ?_ (le_max_right b₀ (a + 1))
    linarith
  have hbd : seriesDefect x (max b₀ (a + 1)) < d :=
    hb₀ (max b₀ (a + 1)) (le_max_left b₀ (a + 1))
  -- IVT on [a, b]
  have hc : ContinuousOn (seriesDefect x) (Icc a (max b₀ (a + 1))) := by
    refine (continuousOn_seriesDefect x hx).mono ?_
    rintro s ⟨h1, -⟩
    exact lt_of_lt_of_le ha1 h1
  obtain ⟨s, hsIcc, hsd⟩ := intermediate_value_Icc' hab hc
    (show d ∈ Icc (seriesDefect x (max b₀ (a + 1))) (seriesDefect x a) by
      constructor
      · exact le_of_lt hbd
      · linarith)
  exact ⟨s, lt_of_lt_of_le ha1 hsIcc.1, hsd⟩

/-- Strict antitonicity of the defect sum on `Ioi x`. -/
theorem strictAnti_seriesDefect (x : ℝ) (hx : 0 < x) :
    StrictAntiOn (seriesDefect x) (Ioi x) := by
  intro s₁ hs₁ s₂ hs₂ hst
  have hA : Summable (seriesTerm x s₁) := summable_seriesTerm hx hs₁
  have hB : Summable (seriesTerm x s₂) := summable_seriesTerm hx hs₂
  have hle : ∀ m, seriesTerm x s₂ m ≤ seriesTerm x s₁ m := by
    intro m
    refine le_of_lt ?_
    have hu1 : (s₁ + (m : ℝ)) / x < (s₂ + (m : ℝ)) / x := by
      rw [div_lt_div_iff₀ hx hx]; exact (mul_lt_mul_of_pos_right (by linarith) hx)
    have hu2 : 1 < (s₁ + (m : ℝ)) / x := by
      rw [one_lt_div₀ hx]; linarith [mem_Ioi.mp hs₁]
    have h3 : 1 < (s₂ + (m : ℝ)) / x := by
      rw [one_lt_div₀ hx]; linarith [mem_Ioi.mp hs₂]
    exact profile_strictAnti (mem_Ioi.mpr hu2) (mem_Ioi.mpr h3) hu1
  have hsum : ∑' m, (seriesTerm x s₁ m - seriesTerm x s₂ m)
      = seriesDefect x s₁ - seriesDefect x s₂ := Summable.tsum_sub hA hB
  have hge : seriesTerm x s₁ 0 - seriesTerm x s₂ 0
      ≤ ∑' m, (seriesTerm x s₁ m - seriesTerm x s₂ m) :=
    Summable.le_tsum (Summable.sub hA hB) 0 (fun j _ => sub_nonneg.mpr (hle j))
  have h0 : seriesTerm x s₂ 0 < seriesTerm x s₁ 0 := by
    have hz : ((0 : ℕ) : ℝ) = 0 := by simp
    have hu1 : (s₁ + (0 : ℕ)) / x < (s₂ + (0 : ℕ)) / x := by
      rw [hz, div_lt_div_iff₀ hx hx]
      exact mul_lt_mul_of_pos_right (by linarith) hx
    have hu2 : 1 < (s₁ + (0 : ℕ)) / x := by
      rw [hz, one_lt_div₀ hx]; linarith [mem_Ioi.mp hs₁]
    have h3 : 1 < (s₂ + (0 : ℕ)) / x := by
      rw [hz, one_lt_div₀ hx]; linarith [mem_Ioi.mp hs₂]
    exact profile_strictAnti (mem_Ioi.mpr hu2) (mem_Ioi.mpr h3) hu1
  have hpos : (0 : ℝ) < seriesDefect x s₁ - seriesDefect x s₂ := by
    rw [← hsum]
    linarith [hge, h0]
  linarith

/-- **Height statement.** For every `x > 0` and `d > 0` there is a unique `y > 0`
with `seriesDefect x (x + y) = d`. -/
theorem existsUnique_seriesDefect (x : ℝ) (hx : 0 < x) {d : ℝ} (hd : 0 < d) :
    ∃! y : ℝ, 0 < y ∧ seriesDefect x (x + y) = d := by
  obtain ⟨s, hsx, hsd⟩ := exists_seriesDefect x hx hd
  refine ⟨s - x, ⟨by linarith, by rw [show x + (s - x) = s by ring]; exact hsd⟩, ?_⟩
  rintro z ⟨hz1, hz2⟩
  by_contra hne
  rcases lt_trichotomy z (s - x) with hlt | heq | hlt
  · have h := strictAnti_seriesDefect x hx
      (mem_Ioi.mpr (show x < x + z by linarith)) (mem_Ioi.mpr hsx)
      (show x + z < s by linarith)
    rw [hz2] at h
    linarith [h, hsd]
  · exact hne heq
  · have h := strictAnti_seriesDefect x hx (mem_Ioi.mpr hsx)
      (mem_Ioi.mpr (show x < x + z by linarith)) (show s < x + z by linarith)
    rw [hz2] at h
    linarith [h, hsd]

end GammaLevel
