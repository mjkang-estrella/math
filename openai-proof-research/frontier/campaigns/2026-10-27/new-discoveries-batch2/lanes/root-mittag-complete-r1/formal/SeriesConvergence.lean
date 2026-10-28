import EulerMoments

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Filter

namespace MittagModulus

theorem gamma_step_ge {x c : ℝ} (hx : 2 ≤ x) (hc : 1 ≤ c) :
    x * Real.Gamma x ≤ Real.Gamma (x + c) := by
  rw [← Real.Gamma_add_one (by linarith : x ≠ 0)]
  exact Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp only [Set.mem_Ici]; linarith)
    (by simp only [Set.mem_Ici]; linarith) (by linarith)

theorem summable_of_arithmetic_subseries {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {m : ℕ} (hm : 0 < m)
    (h : ∀ r : Fin m, Summable (fun n : ℕ => f (n * m + r.val))) : Summable f := by
  have : NeZero m := ⟨by omega⟩
  have hs : Summable (fun x : Fin m × ℕ => f (x.2 * m + x.1.val)) := by
    apply (summable_prod_of_nonneg (fun x => hf _)).2
    exact ⟨h, (hasSum_fintype _).summable⟩
  have hs' : Summable (fun x : ℕ × Fin m => f (x.1 * m + x.2.val)) := by
    exact hs.comp_injective (Equiv.prodComm ℕ (Fin m)).injective
  apply (Nat.divModEquiv m).symm.summable_iff.mp
  change Summable (fun x : ℕ × Fin m => f ((Nat.divModEquiv m).symm x))
  simpa only [Nat.divModEquiv_symm_apply] using hs'

theorem mittag_real_majorant_summable {a b R : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hR : 0 ≤ R) :
    Summable (fun n : ℕ => R ^ n / Real.Gamma (a * (n : ℝ) + b)) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / a)
  have hmcast : 0 < (m : ℝ) := lt_trans (by positivity : 0 < 1 / a) hm
  have hmnat : 0 < m := by exact_mod_cast hmcast
  have hstep : 1 ≤ a * (m : ℝ) := by
    have h := (div_lt_iff₀ ha).mp hm
    nlinarith
  apply summable_of_arithmetic_subseries (fun n => by positivity) hmnat
  intro r
  let M : ℝ := max 2 (2 * R ^ m)
  obtain ⟨N, hN⟩ := exists_nat_gt ((M - a * (r.val : ℝ) - b) / (a * (m : ℝ)))
  have hN' : M < a * (m : ℝ) * (N : ℝ) + a * (r.val : ℝ) + b := by
    have h := (div_lt_iff₀ (mul_pos ha hmcast)).mp hN
    linarith
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [eventually_ge_atTop N] with k hk
  have hkcast : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  let x : ℝ := a * ((k * m + r.val : ℕ) : ℝ) + b
  have hxM : M ≤ x := by
    dsimp [x]
    push_cast
    nlinarith [mul_nonneg (mul_pos ha hmcast).le (sub_nonneg.mpr hkcast)]
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hxM
  have hxB : 2 * R ^ m ≤ x := (le_max_right _ _).trans hxM
  have hxpos : 0 < x := by linarith
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hxpos
  have hH : 0 < Real.Gamma (x + a * (m : ℝ)) := Real.Gamma_pos_of_pos (by positivity)
  have hgam := gamma_step_ge hx2 hstep
  have hbound : 2 * R ^ m * Real.Gamma x ≤ Real.Gamma (x + a * (m : ℝ)) :=
    (mul_le_mul_of_nonneg_right hxB hG.le).trans hgam
  have he : a * (((k + 1) * m + r.val : ℕ) : ℝ) + b = x + a * (m : ℝ) := by
    dsimp [x]
    push_cast
    ring
  have hpow : R ^ ((k + 1) * m + r.val) = R ^ (k * m + r.val) * R ^ m := by
    rw [show (k + 1) * m + r.val = (k * m + r.val) + m by ring, pow_add]
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ R ^ ((k + 1) * m + r.val) / Real.Gamma (a * (((k + 1) * m + r.val : ℕ) : ℝ) + b)),
    abs_of_nonneg (by positivity :
    0 ≤ R ^ (k * m + r.val) / Real.Gamma (a * ((k * m + r.val : ℕ) : ℝ) + b))]
  rw [he, hpow]
  change R ^ (k * m + r.val) * R ^ m / Real.Gamma (x + a * (m : ℝ)) ≤
    (1 / 2 : ℝ) * (R ^ (k * m + r.val) / Real.Gamma x)
  rw [show (1 / 2 : ℝ) * (R ^ (k * m + r.val) / Real.Gamma x) =
    R ^ (k * m + r.val) / (2 * Real.Gamma x) by ring]
  apply (div_le_div_iff₀ hH (by positivity : 0 < 2 * Real.Gamma x)).mpr
  nlinarith [mul_nonneg (pow_nonneg hR (k * m + r.val))
    (sub_nonneg.mpr hbound)]

theorem mittag_complex_series_summable {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (z : ℂ) : Summable (fun n : ℕ => z ^ n / (Real.Gamma (a * (n : ℝ) + b) : ℂ)) := by
  apply Summable.of_norm
  convert mittag_real_majorant_summable ha hb (norm_nonneg z) using 1
  ext n
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.Gamma_pos_of_pos (by positivity))]

noncomputable def mittagLeffler (a b : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / (Real.Gamma (a * (n : ℝ) + b) : ℂ)

theorem hasSum_mittagLeffler {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (Real.Gamma (a * (n : ℝ) + b) : ℂ))
      (mittagLeffler a b z) :=
  (mittag_complex_series_summable ha hb z).hasSum

end MittagModulus
