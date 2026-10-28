import RationalKernel

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MittagModulus

theorem integral_quadratic_reciprocal {v w : ℝ} (hv : 0 < v) (hw : 0 < w) :
    (∫ u in (0 : ℝ)..1, 1 / (v + w * u ^ 2)) =
      Real.arctan (Real.sqrt w / Real.sqrt v) / (Real.sqrt v * Real.sqrt w) := by
  have ha : Real.sqrt v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  have hb : Real.sqrt w ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hw)
  have hd (u : ℝ) : HasDerivAt
      (fun y : ℝ => Real.arctan (Real.sqrt w / Real.sqrt v * y) /
        (Real.sqrt v * Real.sqrt w)) (1 / (v + w * u ^ 2)) u := by
    have hD := ((Real.hasDerivAt_arctan (Real.sqrt w / Real.sqrt v * u)).comp u
      ((hasDerivAt_id u).const_mul (Real.sqrt w / Real.sqrt v))).div_const
        (Real.sqrt v * Real.sqrt w)
    apply hD.congr_deriv
    have hden : v + w * u ^ 2 ≠ 0 := by positivity
    have hden' : 1 + (Real.sqrt w / Real.sqrt v * u) ^ 2 ≠ 0 := by positivity
    field_simp
    ring_nf
    rw [Real.sq_sqrt hv.le, Real.sq_sqrt hw.le]
    ring
  have hcont : Continuous (fun u : ℝ => 1 / (v + w * u ^ 2)) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro u
    exact ne_of_gt (by positivity : 0 < v + w * u ^ 2)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun u _ => hd u) (hcont.intervalIntegrable 0 1)
  simpa only [mul_one, mul_zero, Real.arctan_zero, zero_div, sub_zero] using hi

theorem rationalLaplaceKernel_zero {v w : ℝ} (hv : 0 < v) (hw : 0 < w) :
    rationalLaplaceKernel v w 0 = 1 := by
  unfold rationalLaplaceKernel rationalLaplacePiece
  simp only [mul_zero, Real.exp_zero]
  rw [integral_quadratic_reciprocal hv hw, integral_quadratic_reciprocal hw hv]
  have hr : Real.sqrt v / Real.sqrt w = (Real.sqrt w / Real.sqrt v)⁻¹ := by
    rw [inv_div]
  rw [hr, Real.arctan_inv_of_pos (by positivity : 0 < Real.sqrt w / Real.sqrt v),
    Real.sqrt_mul hv.le w]
  have ha : Real.sqrt v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  have hb : Real.sqrt w ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hw)
  field_simp
  ring

theorem halfProductKernel_zero (v w : ℝ) : halfProductKernel v w 0 = 1 := by
  simp [halfProductKernel]

theorem halfProductKernel_eq_rational {v w : ℝ} (hv : 0 < v) (hw : 0 < w) :
    halfProductKernel v w = rationalLaplaceKernel v w := by
  let H : ℝ → ℝ := fun t => Real.exp ((v + w) * t) *
    (halfProductKernel v w t - rationalLaplaceKernel v w t)
  have hd (t : ℝ) : HasDerivAt H 0 t := by
    have hD := (((hasDerivAt_id t).const_mul (v + w)).exp).mul
      ((halfProductKernel_hasDerivAt v w t).sub (rationalLaplaceKernel_hasDerivAt hv hw t))
    exact hD.congr_deriv (by dsimp only [Pi.sub_apply, id_eq]; ring)
  funext t
  have h := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
    (fun y => (hd y).deriv) t 0
  change Real.exp ((v + w) * t) *
    (halfProductKernel v w t - rationalLaplaceKernel v w t) = _ at h
  simp only [H, mul_zero, Real.exp_zero, halfProductKernel_zero,
    rationalLaplaceKernel_zero hv hw, sub_self, mul_zero] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _))

theorem mixedDifference_congr_positive {f g : ℝ → ℝ}
    (he : ∀ t : ℝ, 0 < t → f t = g t) (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h)
    (t : ℝ) (ht : 0 < t) : mixedDifference hs f t = mixedDifference hs g t := by
  induction hs generalizing t with
  | nil => exact he t ht
  | cons h hs ih =>
    have htail : ∀ u ∈ hs, 0 < u := fun u hu => hhs u (List.mem_cons_of_mem h hu)
    have hh : 0 < h := hhs h (by simp)
    change mixedDifference hs f t - mixedDifference hs f (t + h) =
      mixedDifference hs g t - mixedDifference hs g (t + h)
    rw [ih htail t ht, ih htail (t + h) (by linarith)]

theorem PositiveMixedDifferences.congr_positive {f g : ℝ → ℝ}
    (hf : PositiveMixedDifferences f) (he : ∀ t : ℝ, 0 < t → f t = g t) :
    PositiveMixedDifferences g := by
  intro hs hhs t ht
  rw [← mixedDifference_congr_positive he hs hhs t ht]
  exact hf hs hhs t ht

theorem halfProductKernel_positive {v w : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) :
    PositiveMixedDifferences (halfProductKernel v w) := by
  rcases hv.eq_or_lt with rfl | hv
  · have he : halfProductKernel 0 w = fun t => Real.exp (-w * t) := by
      funext t
      simp [halfProductKernel]
    rw [he]
    exact positiveMixedDifferences_exp hw
  rcases hw.eq_or_lt with rfl | hw
  · have he : halfProductKernel v 0 = fun t => Real.exp (-v * t) := by
      funext t
      simp [halfProductKernel]
    rw [he]
    exact positiveMixedDifferences_exp hv.le
  rw [halfProductKernel_eq_rational hv hw]
  exact rationalLaplaceKernel_positive hv hw

theorem halfCross_positive (v w : ℝ) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    PositiveMixedDifferences (halfCross v w) :=
  (halfProductKernel_positive hv hw).congr_positive
    (fun _t ht => (halfCross_eq_halfProductKernel hv hw ht.le).symm)

theorem source_conjecture_370772 : SourceClaim370772 :=
  sourceClaim_of_halfCross_positive halfCross_positive

end MittagModulus
