import SourceContact
import SecondBranch
open Filter Topology
namespace ContactPilot
noncomputable section

/-- Uniform simultaneous estimates, before converting the normalized roots to w-roots. -/
theorem branch_bounds {u v g h : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (hh : AnalyticAt ℂ h 0)
    (hg₀ : g 0 = 17/4-Complex.I/2) (hh₀ : h 0 = 3-2*Complex.I)
    (hgu : ∀ᶠ x in 𝓝 (0:ℂ), u x = P x+x^5*g x)
    (hhv : ∀ᶠ x in 𝓝 (0:ℂ), v x = -3+x*h x) :
    ∀ᶠ x : ℝ in 𝓝 0, 0 < |x| →
      ((x:ℂ)*u x).im < 0 ∧ ((x:ℂ)*v x).im < 0 ∧
      (1/4:ℝ)*|x|^6 ≤ |((x:ℂ)*u x).im| ∧
      |((x:ℂ)*u x).im| ≤ |x|^6 ∧
      |x|^2 ≤ |((x:ℂ)*v x).im| ∧
      |((x:ℂ)*v x).im| ≤ 3*|x|^2 ∧
      (1/4:ℝ)*|x|^6 ≤ min |((x:ℂ)*u x).im| |((x:ℂ)*v x).im| ∧
      min |((x:ℂ)*u x).im| |((x:ℂ)*v x).im| ≤ |x|^6 := by
  have cg : ContinuousAt (fun x : ℝ => (g x).im) 0 :=
    (Complex.continuous_im.continuousAt.comp
      (hg.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)))
  have ch : ContinuousAt (fun x : ℝ => (h x).im) 0 :=
    (Complex.continuous_im.continuousAt.comp
      (hh.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)))
  have gl : ∀ᶠ x : ℝ in 𝓝 0, -1 < (g x).im :=
    cg.eventually_const_lt (by simp [hg₀]; norm_num)
  have gr : ∀ᶠ x : ℝ in 𝓝 0, (g x).im < -(1/4:ℝ) :=
    cg.eventually_lt_const (by simp [hg₀]; norm_num)
  have hl : ∀ᶠ x : ℝ in 𝓝 0, -3 < (h x).im :=
    ch.eventually_const_lt (by simp [hh₀]; norm_num)
  have hr : ∀ᶠ x : ℝ in 𝓝 0, (h x).im < -1 :=
    ch.eventually_lt_const (by simp [hh₀])
  have egu := (Complex.continuous_ofReal.tendsto (0:ℝ)).eventually (by simpa using hgu)
  have ehv := (Complex.continuous_ofReal.tendsto (0:ℝ)).eventually (by simpa using hhv)
  have small : ∀ᶠ x : ℝ in 𝓝 0, |x| < 1 :=
    continuous_abs.continuousAt.eventually_lt_const (by norm_num)
  filter_upwards [gl, gr, hl, hr, egu, ehv, small] with x hgl hgr hhl hhr hux hvx hsmall
  intro hx
  have iu : ((x:ℂ)*u x).im = |x|^6*(g x).im := by
    simp [hux, P, Complex.mul_im, ← Complex.ofReal_pow, ← abs_pow, abs_of_nonneg (show 0 ≤ x^6 by positivity)]
    ring
  have iv : ((x:ℂ)*v x).im = |x|^2*(h x).im := by
    simp [hvx, Complex.mul_im, ← abs_pow, abs_of_nonneg (even_two.pow_nonneg x)]
    ring
  have p6 : 0 < |x|^6 := pow_pos hx _
  have p2 : 0 < |x|^2 := pow_pos hx _
  have uv : ((x:ℂ)*u x).im < 0 := by rw [iu]; nlinarith
  have vv : ((x:ℂ)*v x).im < 0 := by rw [iv]; nlinarith
  have b6 : (1/4:ℝ)*|x|^6 ≤ |((x:ℂ)*u x).im| := by rw [abs_of_neg uv, iu]; nlinarith
  have c6 : |((x:ℂ)*u x).im| ≤ |x|^6 := by rw [abs_of_neg uv, iu]; nlinarith
  have b2 : |x|^2 ≤ |((x:ℂ)*v x).im| := by rw [abs_of_neg vv, iv]; nlinarith
  have c2 : |((x:ℂ)*v x).im| ≤ 3*|x|^2 := by rw [abs_of_neg vv, iv]; nlinarith
  have le62 : |x|^6 ≤ |x|^2 := by
    calc
      |x|^6 = |x|^2 * |x|^4 := by ring
      _ ≤ |x|^2 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hsmall.le) p2.le
      _ = |x|^2 := mul_one _
  exact ⟨uv, vv, b6, c6, b2, c2, le_min b6 (by linarith), (min_le_left _ _).trans c6⟩
end
end ContactPilot
