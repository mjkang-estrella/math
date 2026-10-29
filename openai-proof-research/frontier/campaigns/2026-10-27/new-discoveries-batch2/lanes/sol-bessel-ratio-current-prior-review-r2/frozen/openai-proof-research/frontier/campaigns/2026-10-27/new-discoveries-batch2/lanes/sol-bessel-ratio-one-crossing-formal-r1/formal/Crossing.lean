import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option warningAsError true

open Set Filter Topology
namespace BesselTransfer

/-- Positivity arbitrarily close to zero; no finite endpoint value is required. -/
def InitiallyPositive (W : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → ∃ z : ℝ, 0 < z ∧ z < x ∧ 0 < W z

/-- Strict increase throughout, or one genuine strict peak. -/
def IncreasingOrPeak (R : ℝ → ℝ) : Prop :=
  StrictMonoOn R (Ioi 0) ∨ ∃ c : ℝ, 0 < c ∧
    StrictMonoOn R (Ioc 0 c) ∧ StrictAntiOn R (Ici c)

/-- Source-compatible shape; monotone and constant cases are included. -/
def Unimodal (R : ℝ → ℝ) : Prop :=
  MonotoneOn R (Ioi 0) ∨ AntitoneOn R (Ioi 0) ∨
    ∃ c : ℝ, 0 < c ∧ MonotoneOn R (Ioc 0 c) ∧ AntitoneOn R (Ici c)

 theorem coeff_nonneg_left {A B x y : ℝ} (hB : 0 ≤ B)
    (hy : 0 < y) (hyx : y ≤ x) (hx : 0 ≤ A / x - B * x) :
    0 ≤ A / y - B * y := by
  have hxpos : 0 < x := lt_of_lt_of_le hy hyx
  have hax : 0 ≤ A - B*x^2 := by
    have := (le_div_iff₀ hxpos).mp (show 0 ≤ (A-B*x^2)/x by
      convert hx using 1; field_simp)
    nlinarith
  have hsq : y^2 ≤ x^2 := sq_le_sq₀ hy.le hxpos.le |>.mpr hyx
  have hab : 0 ≤ A-B*y^2 := by nlinarith [mul_le_mul_of_nonneg_left hsq hB]
  have : 0 ≤ (A-B*y^2)/y := div_nonneg hab hy.le
  convert this using 1; field_simp

 theorem coeff_neg_right {A B x y : ℝ} (hB : 0 ≤ B)
    (hx : 0 < x) (hxy : x ≤ y) (hc : A / x - B*x < 0) :
    A / y - B*y < 0 := by
  by_contra h
  have := coeff_nonneg_left hB hx hxy (le_of_not_gt h)
  linarith

 theorem initial_of_eventually {W : ℝ → ℝ}
    (h : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < W x) : InitiallyPositive W := by
  intro x hx
  have he : ∃ z, z ∈ Ioo (0 : ℝ) x ∧ 0 < W z := by
    have hi : Ioo (0 : ℝ) x ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hx
    exact ((h.and (hi)).exists).imp fun z hz => ⟨hz.2, hz.1⟩
  obtain ⟨z, hz, hw⟩ := he
  exact ⟨z, hz.1, hz.2, hw⟩

 theorem positive_of_coeff_nonneg {W p : ℝ → ℝ} {A B x : ℝ}
    (hB : 0 ≤ B) (hp : ∀ y > 0, 0 < p y)
    (hd : ∀ y > 0, HasDerivAt W ((A/y-B*y)*p y) y)
    (hi : InitiallyPositive W) (hx : 0 < x) (hc : 0 ≤ A/x-B*x) :
    0 < W x := by
  obtain ⟨z, hz, hzx, hw⟩ := hi x hx
  have hm : MonotoneOn W (Icc z x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc z x)
    · exact fun y hy => (hd y (lt_of_lt_of_le hz hy.1)).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (lt_of_lt_of_le hz (interior_subset hy).1)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' := interior_subset hy
      rw [(hd y (lt_of_lt_of_le hz hy'.1)).deriv]
      exact mul_nonneg (coeff_nonneg_left hB (lt_of_lt_of_le hz hy'.1) hy'.2 hc)
        (hp y (lt_of_lt_of_le hz hy'.1)).le
  exact lt_of_lt_of_le hw (hm ⟨le_rfl, hzx.le⟩ ⟨hzx.le, le_rfl⟩ hzx.le)

/-- A nonpositive W forces the potential difference strictly negative; afterwards W
strictly decreases. This handles all A, including A=B=0 without division by B. -/
 theorem forward_crossing {W p : ℝ → ℝ} {A B : ℝ}
    (hB : 0 ≤ B) (hp : ∀ y > 0, 0 < p y)
    (hd : ∀ y > 0, HasDerivAt W ((A/y-B*y)*p y) y)
    (hi : InitiallyPositive W) {x y : ℝ} (hx : 0 < x)
    (hw : W x ≤ 0) (hxy : x < y) : W y < W x := by
  have hc : A/x-B*x < 0 := by
    by_contra hn
    have := positive_of_coeff_nonneg hB hp hd hi hx (le_of_not_gt hn)
    linarith
  have hm : StrictAntiOn W (Ici x) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici x)
    · exact fun z hz => (hd z (lt_of_lt_of_le hx hz)).continuousAt.continuousWithinAt
    · intro z hz
      have hz' : x ≤ z := interior_subset hz
      rw [(hd z (lt_of_lt_of_le hx hz')).deriv]
      exact mul_neg_of_neg_of_pos (coeff_neg_right hB hx hz' hc)
        (hp z (lt_of_lt_of_le hx hz'))
  exact hm (by exact le_refl x) (by exact hxy.le) hxy

 theorem sign_dichotomy {W p : ℝ → ℝ} {A B : ℝ}
    (hB : 0 ≤ B) (hp : ∀ y > 0, 0 < p y)
    (hd : ∀ y > 0, HasDerivAt W ((A/y-B*y)*p y) y)
    (hi : InitiallyPositive W) :
    (∀ x > 0, 0 < W x) ∨ ∃ c : ℝ, 0 < c ∧ W c = 0 ∧
      (∀ x, 0 < x → x < c → 0 < W x) ∧ (∀ x, c < x → W x < 0) := by
  by_cases hall : ∀ x > 0, 0 < W x
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨x, hx, hwx⟩ := hall
    obtain ⟨z, hz, hzx, hwz⟩ := hi x hx
    have hcont : ContinuousOn W (Icc z x) :=
      fun y hy => (hd y (lt_of_lt_of_le hz hy.1)).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hwc⟩ := intermediate_value_Icc' hzx.le hcont ⟨hwx, hwz.le⟩
    have hcpos : 0 < c := lt_of_lt_of_le hz hc.1
    refine ⟨c, hcpos, hwc, ?_, ?_⟩
    · intro y hy hyc
      by_contra hn
      have := forward_crossing hB hp hd hi hy (le_of_not_gt hn) hyc
      rw [hwc] at this
      linarith [le_of_not_gt hn]
    · intro y hcy
      have := forward_crossing hB hp hd hi hcpos hwc.le hcy
      simpa [hwc] using this

end BesselTransfer
