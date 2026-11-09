import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true

namespace LogArctangentSource

/-- The published logarithm--arctangent mean M₂, including its diagonal value. -/
noncomputable def mean (a b : ℝ) : ℝ :=
  if a = b then a else
    (b - a) / (Real.sqrt 2 * Real.arctan ((Real.log b - Real.log a) / Real.sqrt 2))

/-- The source power mean, including its geometric-mean branch. -/
noncomputable def powerMean (p a b : ℝ) : ℝ :=
  if p = 0 then Real.sqrt (a * b) else ((a ^ p + b ^ p) / 2) ^ p⁻¹

noncomputable def resultant (p q a b : ℝ) : ℝ :=
  powerMean p (mean a (powerMean q a b)) (mean (powerMean q a b) b)

/-- Both parameter branches of published Conjecture 37. -/
def SourceClaim : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b →
    mean a b < resultant (Real.sqrt 17) ((5 - Real.sqrt 17) / 2) a b ∧
    mean a b < resultant (-Real.sqrt 17) ((5 + Real.sqrt 17) / 2) a b

theorem mean_self (a : ℝ) : mean a a = a := by simp [mean]

theorem mean_symm (a b : ℝ) : mean a b = mean b a := by
  by_cases h : a = b
  · subst b; rfl
  · rw [mean, mean, ite_eq_right h, ite_eq_right (Ne.symm h)]
    rw [show Real.log a - Real.log b = -(Real.log b - Real.log a) by ring,
      neg_div, Real.arctan_neg, mul_neg, div_neg]
    ring

theorem mean_pos_of_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) : 0 < mean a b := by
  rw [mean, ite_eq_right (ne_of_lt hab)]
  exact div_pos (sub_pos.mpr hab)
    (mul_pos (Real.sqrt_pos.mpr (by norm_num))
      (Real.arctan_pos.mpr (div_pos (sub_pos.mpr (Real.log_lt_log ha hab))
        (Real.sqrt_pos.mpr (by norm_num)))))

theorem mean_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < mean a b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact mean_pos_of_lt ha hab
  · subst b; simpa only [mean_self] using ha
  · rw [mean_symm]; exact mean_pos_of_lt hb hab

theorem mean_homogeneous {a b k : ℝ} (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    mean (k * a) (k * b) = k * mean a b := by
  by_cases hab : a = b
  · subst b; simp only [mean_self]
  · have hkab : k * a ≠ k * b := fun h => hab ((mul_left_cancel₀ hk.ne') h)
    rw [mean, mean, ite_eq_right hkab, ite_eq_right hab,
      Real.log_mul hk.ne' hb.ne', Real.log_mul hk.ne' ha.ne']
    rw [show Real.log k + Real.log b - (Real.log k + Real.log a) =
      Real.log b - Real.log a by ring]
    ring

theorem powerMean_symm (p a b : ℝ) : powerMean p a b = powerMean p b a := by
  simp only [powerMean, mul_comm a b, add_comm (a ^ p) (b ^ p)]

theorem powerMean_pos {p a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < powerMean p a b := by
  unfold powerMean
  split_ifs
  · exact Real.sqrt_pos.mpr (mul_pos ha hb)
  · exact Real.rpow_pos_of_pos
      (div_pos (add_pos (Real.rpow_pos_of_pos ha p) (Real.rpow_pos_of_pos hb p))
        (by norm_num)) _

theorem powerMean_self {p a : ℝ} (ha : 0 < a) : powerMean p a a = a := by
  by_cases hp : p = 0
  · simp only [powerMean, ite_eq_left hp]
    exact Real.sqrt_mul_self ha.le
  · rw [powerMean, ite_eq_right hp, show (a ^ p + a ^ p) / 2 = a ^ p by ring,
      ← Real.rpow_mul ha.le, mul_inv_cancel₀ hp, Real.rpow_one]

theorem powerMean_homogeneous {p a b k : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    powerMean p (k * a) (k * b) = k * powerMean p a b := by
  by_cases hp : p = 0
  · rw [powerMean, powerMean, ite_eq_left hp, ite_eq_left hp,
      show k * a * (k * b) = k ^ 2 * (a * b) by ring,
      Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk.le]
  · rw [powerMean, powerMean, ite_eq_right hp, ite_eq_right hp,
      Real.mul_rpow hk.le ha.le, Real.mul_rpow hk.le hb.le,
      show (k ^ p * a ^ p + k ^ p * b ^ p) / 2 =
        k ^ p * ((a ^ p + b ^ p) / 2) by ring,
      Real.mul_rpow (Real.rpow_nonneg hk.le _) (by positivity),
      ← Real.rpow_mul hk.le, mul_inv_cancel₀ hp, Real.rpow_one]

theorem powerMean_strict_mono {p a b c d : ℝ} (hp : p ≠ 0)
    (ha : 0 < a) (hb : 0 < b) (hac : a < c) (hbd : b < d) :
    powerMean p a b < powerMean p c d := by
  have hc : 0 < c := ha.trans hac
  have hd : 0 < d := hb.trans hbd
  rw [powerMean, powerMean, ite_eq_right hp, ite_eq_right hp]
  rcases hp.lt_or_gt with hp | hp
  · apply Real.rpow_lt_rpow_of_neg (by positivity) _ (inv_lt_zero.mpr hp)
    exact div_lt_div_of_pos_right
      (add_lt_add (Real.rpow_lt_rpow_of_neg ha hac hp)
        (Real.rpow_lt_rpow_of_neg hb hbd hp)) (by norm_num)
  · apply Real.rpow_lt_rpow (by positivity) _ (inv_pos.mpr hp)
    exact div_lt_div_of_pos_right
      (add_lt_add (Real.rpow_lt_rpow ha.le hac hp)
        (Real.rpow_lt_rpow hb.le hbd hp)) (by norm_num)

theorem powerMean_strict_mono_left {p a b c : ℝ} (hp : p ≠ 0)
    (ha : 0 < a) (hb : 0 < b) (hac : a < c) :
    powerMean p a b < powerMean p c b := by
  have hc : 0 < c := ha.trans hac
  rw [powerMean, powerMean, ite_eq_right hp, ite_eq_right hp]
  rcases hp.lt_or_gt with hp | hp
  · apply Real.rpow_lt_rpow_of_neg (by positivity) _ (inv_lt_zero.mpr hp)
    exact div_lt_div_of_pos_right
      (by linarith [Real.rpow_lt_rpow_of_neg ha hac hp]) (by norm_num)
  · apply Real.rpow_lt_rpow (by positivity) _ (inv_pos.mpr hp)
    exact div_lt_div_of_pos_right
      (by linarith [Real.rpow_lt_rpow ha.le hac hp]) (by norm_num)

theorem powerMean_strict_mono_right {p a b d : ℝ} (hp : p ≠ 0)
    (ha : 0 < a) (hb : 0 < b) (hbd : b < d) :
    powerMean p a b < powerMean p a d := by
  rw [powerMean_symm p a b, powerMean_symm p a d]
  exact powerMean_strict_mono_left hp hb ha hbd

theorem powerMean_between {p a b : ℝ} (hp : p ≠ 0)
    (ha : 0 < a) (hab : a < b) : a < powerMean p a b ∧ powerMean p a b < b := by
  have hb := ha.trans hab
  constructor
  · have h := powerMean_strict_mono_right (p := p) hp ha ha hab
    simpa only [powerMean_self ha] using h
  · have h := powerMean_strict_mono_left (p := p) hp ha hb hab
    simpa only [powerMean_self hb] using h

theorem resultant_symm (p q a b : ℝ) : resultant p q a b = resultant p q b a := by
  unfold resultant
  rw [powerMean_symm q b a, mean_symm b, mean_symm (powerMean q a b) a,
    powerMean_symm p]

theorem resultant_pos {p q a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < resultant p q a b := by
  exact powerMean_pos (mean_pos ha (powerMean_pos ha hb))
    (mean_pos (powerMean_pos ha hb) hb)

theorem resultant_homogeneous {p q a b k : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    resultant p q (k * a) (k * b) = k * resultant p q a b := by
  unfold resultant
  rw [powerMean_homogeneous ha hb hk,
    mean_homogeneous ha (powerMean_pos ha hb) hk,
    mean_homogeneous (powerMean_pos ha hb) hb hk,
    powerMean_homogeneous (mean_pos ha (powerMean_pos ha hb))
      (mean_pos (powerMean_pos ha hb) hb) hk]

end LogArctangentSource
