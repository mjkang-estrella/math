import MeanSourceDefs

set_option autoImplicit false
set_option warningAsError true

namespace LogArctangentSource

noncomputable def d : ℝ := Real.sqrt 17
noncomputable def alpha : ℝ := (5 + d) / 2
noncomputable def beta : ℝ := (5 - d) / 2

 theorem d_bounds : 4 < d ∧ d < 5 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  have hp := Real.sqrt_nonneg (17 : ℝ)
  dsimp [d]
  constructor <;> nlinarith

theorem parameters : 0 < beta ∧ beta < alpha ∧ alpha - beta = d ∧ alpha * beta = 2 := by
  obtain ⟨h1,h2⟩ := d_bounds
  have hs : d ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  dsimp [alpha, beta]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · ring
  · nlinarith

/-- Generic positive-parameter Stolarsky expression, diagonal extended. -/
noncomputable def stolarsky (r q a b : ℝ) : ℝ :=
  if a = b then a else (q / r * ((b ^ r - a ^ r) / (b ^ q - a ^ q))) ^ (r - q)⁻¹

noncomputable def fixedS (a b : ℝ) : ℝ := stolarsky alpha beta a b
noncomputable def centeredLogGap (t : ℝ) : ℝ :=
  Real.log (fixedS (Real.exp (-t)) (Real.exp t)) -
    Real.log (mean (Real.exp (-t)) (Real.exp t))

theorem stolarsky_symm (r q a b : ℝ) : stolarsky r q a b = stolarsky r q b a := by
  by_cases h : a = b
  · subst b; rfl
  · simp only [stolarsky, ite_eq_right h, ite_eq_right (Ne.symm h)]
    congr 2
    rw [show a ^ r - b ^ r = -(b ^ r - a ^ r) by ring,
      show a ^ q - b ^ q = -(b ^ q - a ^ q) by ring, neg_div_neg_eq]

theorem stolarsky_base_pos {r q a b : ℝ} (hr : 0 < r) (hq : 0 < q)
    (ha : 0 < a) (hab : a < b) :
    0 < q / r * ((b ^ r - a ^ r) / (b ^ q - a ^ q)) := by
  exact mul_pos (div_pos hq hr) (div_pos
    (sub_pos.mpr (Real.rpow_lt_rpow ha.le hab hr))
    (sub_pos.mpr (Real.rpow_lt_rpow ha.le hab hq)))

theorem stolarsky_pos {r q a b : ℝ} (hr : 0 < r) (hq : 0 < q)
    (ha : 0 < a) (hb : 0 < b) : 0 < stolarsky r q a b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [stolarsky, ite_eq_right hab.ne]
    exact Real.rpow_pos_of_pos (stolarsky_base_pos hr hq ha hab) _
  · subst b; simpa [stolarsky] using ha
  · rw [stolarsky_symm, stolarsky, ite_eq_right hab.ne]
    exact Real.rpow_pos_of_pos (stolarsky_base_pos hr hq hb hab) _

theorem stolarsky_power {r q a b : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hp : r - q ≠ 0) (ha : 0 < a) (hab : a < b) :
    (stolarsky r q a b) ^ (r - q) =
      q / r * ((b ^ r - a ^ r) / (b ^ q - a ^ q)) := by
  rw [stolarsky, ite_eq_right hab.ne,
    ← Real.rpow_mul (stolarsky_base_pos hr hq ha hab).le,
    inv_mul_cancel₀ hp, Real.rpow_one]

theorem powerMean_power {p a b : ℝ} (hp : p ≠ 0) (ha : 0 < a) (hb : 0 < b) :
    powerMean p a b ^ p = (a ^ p + b ^ p) / 2 := by
  rw [powerMean, ite_eq_right hp, ← Real.rpow_mul (by positivity),
    inv_mul_cancel₀ hp, Real.rpow_one]

theorem stolarsky_stabilization {r q a b : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hp : r - q ≠ 0) (ha : 0 < a) (hab : a < b) :
    powerMean (r-q) (stolarsky r q a (powerMean q a b))
      (stolarsky r q (powerMean q a b) b) = stolarsky r q a b := by
  have hb := ha.trans hab
  let c := powerMean q a b
  have hc : 0 < c := powerMean_pos ha hb
  obtain ⟨hac,hcb⟩ := powerMean_between hq.ne' ha hab
  change a < c at hac
  change c < b at hcb
  have hmid : c ^ q = (a ^ q + b ^ q) / 2 := powerMean_power hq.ne' ha hb
  have hden : b ^ q - a ^ q ≠ 0 :=
    (sub_pos.mpr (Real.rpow_lt_rpow ha.le hab hq)).ne'
  apply Real.rpow_left_injOn hp (powerMean_pos
    (stolarsky_pos hr hq ha hc) (stolarsky_pos hr hq hc hb)).le
    (stolarsky_pos hr hq ha hb).le
  change powerMean (r-q) (stolarsky r q a c) (stolarsky r q c b) ^ (r-q) = stolarsky r q a b ^ (r-q)
  rw [powerMean_power hp (stolarsky_pos hr hq ha hc) (stolarsky_pos hr hq hc hb),
    stolarsky_power hr hq hp ha hac, stolarsky_power hr hq hp hc hcb,
    stolarsky_power hr hq hp ha hab, hmid]
  rw [show (a ^ q + b ^ q) / 2 - a ^ q = (b ^ q - a ^ q)/2 by ring,
    show b ^ q - (a ^ q + b ^ q) / 2 = (b ^ q - a ^ q)/2 by ring]
  field_simp [hden]
  ring

theorem stolarsky_homogeneous_lt {r q a b k : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hp : r-q ≠ 0) (ha : 0 < a) (hab : a < b) (hk : 0 < k) :
    stolarsky r q (k*a) (k*b) = k * stolarsky r q a b := by
  have hb := ha.trans hab
  have hs := stolarsky_pos hr hq ha hb
  apply Real.rpow_left_injOn hp (stolarsky_pos hr hq (mul_pos hk ha) (mul_pos hk hb)).le
    (mul_pos hk hs).le
  change stolarsky r q (k*a) (k*b) ^ (r-q) = (k * stolarsky r q a b) ^ (r-q)
  rw [stolarsky_power hr hq hp (mul_pos hk ha) (mul_lt_mul_of_pos_left hab hk),
    Real.mul_rpow hk.le hs.le, stolarsky_power hr hq hp ha hab,
    Real.mul_rpow hk.le hb.le, Real.mul_rpow hk.le ha.le,
    Real.mul_rpow hk.le hb.le, Real.mul_rpow hk.le ha.le,
    Real.rpow_sub hk]
  have hkr := (Real.rpow_pos_of_pos hk r).ne'
  have hkq := (Real.rpow_pos_of_pos hk q).ne'
  have hden := (sub_pos.mpr (Real.rpow_lt_rpow ha.le hab hq)).ne'
  field_simp

theorem stolarsky_homogeneous {r q a b k : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hp : r-q ≠ 0) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    stolarsky r q (k*a) (k*b) = k * stolarsky r q a b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact stolarsky_homogeneous_lt hr hq hp ha hab hk
  · subst b; simp [stolarsky]
  · rw [stolarsky_symm r q (k*a), stolarsky_symm r q a]
    exact stolarsky_homogeneous_lt hr hq hp hb hab hk

theorem fixedS_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < fixedS a b :=
  stolarsky_pos (parameters.1.trans parameters.2.1) parameters.1 ha hb

theorem fixedS_symm (a b : ℝ) : fixedS a b = fixedS b a := stolarsky_symm _ _ _ _

theorem fixedS_homogeneous {a b k : ℝ} (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    fixedS (k*a) (k*b) = k * fixedS a b := by
  exact stolarsky_homogeneous (parameters.1.trans parameters.2.1) parameters.1
    (by rw [parameters.2.2.1]; exact (lt_trans (by norm_num) d_bounds.1).ne') ha hb hk

theorem fixedS_stabilization_positive {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    powerMean d (fixedS a (powerMean beta a b))
      (fixedS (powerMean beta a b) b) = fixedS a b := by
  simpa only [fixedS, parameters.2.2.1] using
    stolarsky_stabilization (parameters.1.trans parameters.2.1) parameters.1
      (show alpha-beta ≠ 0 by linarith [parameters.2.1]) ha hab

theorem stolarsky_swap {r q a b : ℝ} (hr : 0 < r) (hq : 0 < q)
    (ha : 0 < a) (hab : a < b) : stolarsky q r a b = stolarsky r q a b := by
  have hbase := stolarsky_base_pos hr hq ha hab
  have hdr := (sub_pos.mpr (Real.rpow_lt_rpow ha.le hab hr)).ne'
  have hdq := (sub_pos.mpr (Real.rpow_lt_rpow ha.le hab hq)).ne'
  rw [stolarsky, stolarsky, ite_eq_right hab.ne, ite_eq_right hab.ne]
  have hinv : r/q * ((b^q-a^q)/(b^r-a^r)) =
      (q/r * ((b^r-a^r)/(b^q-a^q)))⁻¹ := by
    field_simp
  rw [hinv, show q-r = -(r-q) by ring, inv_neg, Real.inv_rpow hbase.le,
    Real.rpow_neg hbase.le, inv_inv]

theorem fixedS_stabilization_negative {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    powerMean (-d) (fixedS a (powerMean alpha a b))
      (fixedS (powerMean alpha a b) b) = fixedS a b := by
  have hb := ha.trans hab
  obtain ⟨hac,hcb⟩ := powerMean_between (parameters.1.trans parameters.2.1).ne' ha hab
  have hc := powerMean_pos (p := alpha) ha hb
  have hs := stolarsky_stabilization parameters.1 (parameters.1.trans parameters.2.1)
    (show beta-alpha ≠ 0 by linarith [parameters.2.1]) ha hab
  rw [show beta-alpha = -d by linarith [parameters.2.2.1],
    stolarsky_swap (parameters.1.trans parameters.2.1) parameters.1 ha hac,
    stolarsky_swap (parameters.1.trans parameters.2.1) parameters.1 hc hcb,
    stolarsky_swap (parameters.1.trans parameters.2.1) parameters.1 ha hab] at hs
  exact hs

theorem mean_log_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    mean a b = (b-a)/(Real.sqrt 2 * Real.arctan (Real.log (b/a)/Real.sqrt 2)) := by
  rw [Real.log_div hb.ne' ha.ne', mean, ite_eq_right hab]

theorem fixedS_self (a : ℝ) : fixedS a a = a := by simp [fixedS, stolarsky]

/-- Identifies the generic implementation with the requested literal fixed mean. -/
theorem fixedS_formula {a b : ℝ} (hab : a ≠ b) :
    fixedS a b = (beta/alpha * ((b^alpha-a^alpha)/(b^beta-a^beta))) ^ (1/d) := by
  simp only [fixedS, stolarsky, ite_eq_right hab, parameters.2.2.1, one_div]

end LogArctangentSource
