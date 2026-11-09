import MeanDerivatives
import Transfer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
set_option autoImplicit false
set_option warningAsError true
namespace LogArctangentMean
open LogArctangentSource (alpha beta)
theorem d_source : d = LogArctangentSource.d := rfl

theorem B_factor (t : ℝ) :
    B t = Real.sinh t * Real.sinh (alpha*t) * Real.sinh (beta*t) := by
  have h5 : 5*t = alpha*t + beta*t := by dsimp [alpha, beta]; ring
  have hd : d*t = alpha*t - beta*t := by dsimp [alpha, beta]; rw [d_source]; ring
  rw [B, h5, hd, Real.cosh_add, Real.cosh_sub]
  ring

theorem A_factor (t : ℝ) :
    A t = ((5-d)/(2*d))*Real.sinh (d*t)*Real.sinh t +
      Real.sinh (((d+3)/2)*t)*Real.sinh (beta*t) := by
  have hsum : ((d+3)/2)*t + beta*t = 4*t := by dsimp [beta]; rw [d_source]; ring
  have hsub : ((d+3)/2)*t - beta*t = d*t-t := by dsimp [beta]; rw [d_source]; ring
  have h := Real.cosh_add (((d+3)/2)*t) (beta*t)
  have h' := Real.cosh_sub (((d+3)/2)*t) (beta*t)
  rw [hsum] at h
  rw [hsub, Real.cosh_sub] at h'
  unfold A
  have hd := d_ne
  field_simp
  simp only [mul_comm d t, mul_comm beta t,
    show (d+3)/2*t = t*(d+3)/2 by ring] at h h'
  linear_combination d * h - d * h'

theorem B_pos {t : ℝ} (ht : 0 < t) : 0 < B t := by
  rw [B_factor]
  exact mul_pos (mul_pos (Real.sinh_pos_iff.mpr ht)
    (Real.sinh_pos_iff.mpr (mul_pos
      (LogArctangentSource.parameters.1.trans LogArctangentSource.parameters.2.1) ht)))
    (Real.sinh_pos_iff.mpr (mul_pos LogArctangentSource.parameters.1 ht))

theorem A_pos {t : ℝ} (ht : 0 < t) : 0 < A t := by
  rw [A_factor]
  have hd : 0 < d := lt_trans (by norm_num) d_bounds.1
  have h5 : d < 5 := lt_trans d_bounds.2 (by norm_num)
  exact add_pos
    (mul_pos (mul_pos (div_pos (sub_pos.mpr h5) (mul_pos (by norm_num) hd))
      (Real.sinh_pos_iff.mpr (mul_pos hd ht))) (Real.sinh_pos_iff.mpr ht))
    (mul_pos (Real.sinh_pos_iff.mpr (mul_pos (by positivity) ht))
      (Real.sinh_pos_iff.mpr (mul_pos LogArctangentSource.parameters.1 ht)))

noncomputable def J (t : ℝ) : ℝ := Real.sqrt 2 * B t / ((1+2*t^2)*A t)

theorem hasDerivAt_J {t : ℝ} (ht : 0 < t) :
    HasDerivAt J
      (Real.sqrt 2 * (deriv B t * ((1+2*t^2)*A t) -
        B t * (4*t*A t + (1+2*t^2)*deriv A t)) / (((1+2*t^2)*A t)^2)) t := by
  have hp : 0 < 1+2*t^2 := by positivity
  have hden : (1+2*t^2)*A t ≠ 0 := (mul_pos hp (A_pos ht)).ne'
  have hpoly : HasDerivAt (fun x : ℝ => 1+2*x^2) (4*t) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul 2).const_add 1 using 1
    · funext x; dsimp
    · dsimp; ring
  convert (((hasDerivAt_B t).const_mul (Real.sqrt 2)).div
    (hpoly.mul (hasDerivAt_A t)) hden) using 1
  · rfl
  · dsimp; rw [← deriv_A, ← deriv_B]; ring

theorem J_derivative_identity {t : ℝ} (ht : 0 < t) :
    deriv J t - Real.sqrt 2 / (1+2*t^2) =
      Real.sqrt 2 * E t / ((1+2*t^2)^2 * A t^2) := by
  rw [(hasDerivAt_J ht).deriv]
  have hA := (A_pos ht).ne'
  have hp : 1+2*t^2 ≠ 0 := ne_of_gt (by positivity)
  unfold E U V
  field_simp
  ring
open Filter Topology

theorem sinh_scaled_limit (c : ℝ) :
    Tendsto (fun t : ℝ => Real.sinh (c*t)/t) (𝓝[>] 0) (𝓝 c) := by
  have h := (((hasDerivAt_id (0:ℝ)).const_mul c).sinh).tendsto_slope_zero_right
  simpa [div_eq_mul_inv, mul_comm] using h

theorem A_scaled_limit :
    Tendsto (fun t : ℝ => A t/t^2) (𝓝[>] 0) (𝓝 2) := by
  have h := (((sinh_scaled_limit d).mul (sinh_scaled_limit 1)).const_mul
    ((5-d)/(2*d))).add ((sinh_scaled_limit ((d+3)/2)).mul (sinh_scaled_limit beta))
  have hc : ((5-d)/(2*d))*(d*1)+((d+3)/2)*beta = 2 := by
    dsimp [beta]; rw [← d_source]; field_simp [d_ne]; nlinarith [d_sq]
  rw [hc] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : t ≠ 0 := ne_of_gt ht
  rw [A_factor]
  simp only [one_mul]
  field_simp

theorem B_scaled_limit :
    Tendsto (fun t : ℝ => B t/t^3) (𝓝[>] 0) (𝓝 2) := by
  have h := ((sinh_scaled_limit 1).mul (sinh_scaled_limit alpha)).mul
    (sinh_scaled_limit beta)
  simpa only [one_mul, LogArctangentSource.parameters.2.2.2] using
    h.congr' (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [B_factor]; simp only [one_mul]; ring)

theorem J_limit : Tendsto J (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hp : Tendsto (fun t : ℝ => 1+2*t^2) (𝓝[>] 0) (𝓝 (1+2*(0:ℝ)^2)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (ht.pow 2))
  have h := (ht.mul (B_scaled_limit.const_mul (Real.sqrt 2))).div
    (hp.mul A_scaled_limit) (by norm_num : (1+2*(0:ℝ)^2)*2 ≠ 0)
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  dsimp [J]
  have hn : t ≠ 0 := ne_of_gt ht
  field_simp
theorem hasDerivAt_centered_arctan (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.arctan (Real.sqrt 2*x))
      (Real.sqrt 2/(1+2*t^2)) t := by
  convert (((hasDerivAt_id t).const_mul (Real.sqrt 2)).arctan) using 1
  · rfl
  · dsimp
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring

theorem J_gt_arctan (hE : ∀ t : ℝ, 0 < t → 0 < E t) {t : ℝ} (ht : 0 < t) :
    Real.arctan (Real.sqrt 2*t) < J t := by
  let F : ℝ → ℝ := fun x => J x - Real.arctan (Real.sqrt 2*x)
  have hd (x : ℝ) (hx : 0 < x) : HasDerivAt F
      (Real.sqrt 2 * E x / ((1+2*x^2)^2*A x^2)) x := by
    have h := (hasDerivAt_J hx).sub (hasDerivAt_centered_arctan x)
    convert h using 1
    rw [← J_derivative_identity hx, (hasDerivAt_J hx).deriv]
  have hm : StrictMonoOn F (Set.Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
      rw [(hd x hx').deriv]
      exact div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (hE x hx'))
        (mul_pos (sq_pos_of_pos (by positivity)) (sq_pos_of_pos (A_pos hx')))
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have ha : Tendsto (fun x : ℝ => Real.arctan (Real.sqrt 2*x)) (𝓝[>] 0)
        (𝓝 (Real.arctan (Real.sqrt 2*0))) :=
      (hasDerivAt_centered_arctan 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    simpa [F] using J_limit.sub ha
  have hn (y : ℝ) (hy : 0 < y) : 0 ≤ F y := by
    apply le_of_tendsto hlim
    have he : ∀ᶠ x : ℝ in 𝓝[>] 0, x < y :=
      (eventually_lt_nhds hy).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, he] with x hx hxy
    exact (hm hx hy hxy).le
  have h := (hn (t/2) (by linarith)).trans_lt (hm (by change 0 < t/2; linarith) ht (by linarith))
  exact sub_pos.mp h
end LogArctangentMean
