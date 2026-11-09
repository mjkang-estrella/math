import RootLocalization
import BidiskStable
namespace ContactPilot
noncomputable section

 theorem beta_denominator_ne (y : ℂ) (hy : 0 ≤ y.im) :
    1-Complex.I*y ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  simp [Complex.mul_re] at hr
  linarith

 theorem betaInv_beta (y : ℂ) (hy : 1-Complex.I*y ≠ 0) :
    betaInv (beta y) = y := by
  unfold betaInv beta
  field_simp
  ring_nf
  simp [Complex.I_sq]

 theorem one_add_beta_ne (y : ℂ) (hy : 1-Complex.I*y ≠ 0) :
    1+beta y ≠ 0 := by
  unfold beta
  rw [one_add_div hy]
  apply div_ne_zero
  · ring_nf
    norm_num
  · exact hy

 theorem one_sub_beta_real_ne (x : ℝ) (hx : x ≠ 0) :
    1-beta (x:ℂ) ≠ 0 := by
  have hd := beta_denominator_ne (x:ℂ) (by simp)
  unfold beta
  rw [one_sub_div hd]
  apply div_ne_zero
  · have hc : (x:ℂ) ≠ 0 := by exact_mod_cast hx
    have he : 1-Complex.I*(x:ℂ) - (1+Complex.I*(x:ℂ)) =
        -2*Complex.I*(x:ℂ) := by ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hc
  · exact hd

 theorem betaInv_neg_beta_real (x : ℝ) (hx : x ≠ 0) :
    betaInv (-beta (x:ℂ)) = -1/(x:ℂ) := by
  have hc : (x:ℂ) ≠ 0 := by exact_mod_cast hx
  have hd := beta_denominator_ne (x:ℂ) (by simp)
  have hb := one_sub_beta_real_ne x hx
  unfold betaInv
  rw [show 1+-beta (x:ℂ) = 1-beta (x:ℂ) by ring]
  apply (div_eq_iff hb).mpr
  unfold beta
  field_simp
  ring

 theorem conjugate_R_real (x : ℝ) (hx : x ≠ 0) (y : ℂ) :
    star (R (x:ℂ) (star y)) = (x:ℂ)^3 *
      (Q (-1/(x:ℂ)) y + Complex.I*N (-1/(x:ℂ)) y) := by
  have hc : (x:ℂ) ≠ 0 := by exact_mod_cast hx
  rw [R_from_quotient _ _ hc]
  simp [Q, N]

/-- Clearing and conjugation identify the actual numerator zero set.
The source parameter is real and nonzero, and the second chart avoids -1. -/
 theorem numerator_root_iff (x : ℝ) (hx : x ≠ 0) (v : ℂ)
    (hv : 1+v ≠ 0) :
    eval₂ bidiskNumerator (-beta (x:ℂ)) v = 0 ↔
      R (x:ℂ) (star (betaInv v)) = 0 := by
  have hz : 1+-beta (x:ℂ) ≠ 0 := by
    simpa only [sub_eq_add_neg] using one_sub_beta_real_ne x hx
  have hclear : eval₂ bidiskNumerator (-beta (x:ℂ)) v =
      (1+-beta (x:ℂ))^3*(1+v)^2 *
        (Q (-1/(x:ℂ)) (betaInv v) + Complex.I*N (-1/(x:ℂ)) (betaInv v)) := by
    simp only [bidiskNumerator, eval₂, map_add, map_mul, MvPolynomial.eval_C]
    change eval₂ cayleyQ _ _ + Complex.I*eval₂ cayleyN _ _ = _
    rw [cayleyQ_clearing _ _ hz hv, cayleyN_clearing _ _ hz hv,
      betaInv_neg_beta_real x hx, eval_q, eval_n]
    unfold Q N
    ring
  have hfac := mul_ne_zero (pow_ne_zero 3 hz) (pow_ne_zero 2 hv)
  rw [hclear, mul_eq_zero, or_iff_right hfac]
  have hc : (x:ℂ)^3 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hx)
  have he := conjugate_R_real x hx (betaInv v)
  constructor
  · intro h
    rw [h, mul_zero] at he
    exact star_eq_zero.mp he
  · intro h
    rw [h, star_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hc

 theorem pole_root_maps_to_numerator (x : ℝ) (hx : x ≠ 0) (u : ℂ)
    (hi : u.im < 0) (hr : R (x:ℂ) u = 0) :
    eval₂ bidiskNumerator (-beta (x:ℂ)) (beta (star u)) = 0 := by
  have hd : 1-Complex.I*star u ≠ 0 :=
    beta_denominator_ne _ (by simpa using hi.le)
  apply (numerator_root_iff x hx _ (one_add_beta_ne _ hd)).mpr
  rwa [betaInv_beta _ hd, star_star]
end
end ContactPilot
