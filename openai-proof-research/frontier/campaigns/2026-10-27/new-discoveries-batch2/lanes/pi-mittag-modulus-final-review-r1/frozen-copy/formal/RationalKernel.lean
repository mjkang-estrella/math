import HalfKernel
import CompactParameter

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MittagModulus

noncomputable def rationalLaplacePiece (v w t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, Real.exp (-w * (1 - u ^ 2) * t) / (v + w * u ^ 2)

noncomputable def rationalLaplaceKernel (v w t : ℝ) : ℝ :=
  (2 * Real.sqrt (v * w) / Real.pi) *
    (rationalLaplacePiece v w t + rationalLaplacePiece w v t)

theorem rationalLaplacePiece_positive {v w : ℝ} (hv : 0 < v) (hw : 0 ≤ w) :
    PositiveMixedDifferences (rationalLaplacePiece v w) := by
  unfold rationalLaplacePiece
  apply PositiveMixedDifferences.intervalIntegral zero_le_one
  · intro t
    apply Continuous.continuousOn
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro u
    exact ne_of_gt (add_pos_of_pos_of_nonneg hv (mul_nonneg hw (sq_nonneg u)))
  · intro u hu
    have hell : 0 ≤ w * (1 - u ^ 2) := by
      apply mul_nonneg hw
      nlinarith [mul_self_le_mul_self hu.1 hu.2]
    have hd : 0 ≤ 1 / (v + w * u ^ 2) := by positivity
    convert (positiveMixedDifferences_exp hell).const_mul hd using 1
    funext t
    ring_nf

theorem rationalLaplaceKernel_positive {v w : ℝ} (hv : 0 < v) (hw : 0 < w) :
    PositiveMixedDifferences (rationalLaplaceKernel v w) := by
  exact ((rationalLaplacePiece_positive hv hw.le).add
    (rationalLaplacePiece_positive hw hv.le)).const_mul (by positivity)

theorem halfExpIntegral_hasDerivAt (x : ℝ) :
    HasDerivAt halfExpIntegral
      (∫ u in (0 : ℝ)..1, u ^ 2 * Real.exp (x * u ^ 2)) x := by
  unfold halfExpIntegral
  refine hasDerivAt_unitIntegral
    (F := fun y u : ℝ => Real.exp (y * u ^ 2))
    (F' := fun y u : ℝ => u ^ 2 * Real.exp (y * u ^ 2))
    (by fun_prop) (by fun_prop) ?_ x
  intro y u
  simpa only [id_eq, one_mul, mul_one, mul_comm] using ((hasDerivAt_id y).mul_const (u ^ 2)).exp

theorem halfExpIntegral_ode (x : ℝ) :
    halfExpIntegral x + 2 * x * deriv halfExpIntegral x = Real.exp x := by
  have hd (u : ℝ) : HasDerivAt (fun y : ℝ => y * Real.exp (x * y ^ 2))
      (Real.exp (x * u ^ 2) + 2 * x * (u ^ 2 * Real.exp (x * u ^ 2))) u := by
    convert (hasDerivAt_id u).mul (((hasDerivAt_id u).pow 2).const_mul x).exp using 1 <;>
      (try funext y) <;> norm_num
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun u _ => hd u)
    (by apply Continuous.intervalIntegrable; fun_prop)
  rw [intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul] at hi
  simp only [one_pow, mul_one, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    Real.exp_zero, one_mul, sub_zero] at hi
  rw [(halfExpIntegral_hasDerivAt x).deriv]
  simpa only [halfExpIntegral] using hi

theorem rationalLaplacePiece_hasDerivAt {v w : ℝ} (hv : 0 < v) (hw : 0 ≤ w) (t : ℝ) :
    HasDerivAt (rationalLaplacePiece v w)
      (∫ u in (0 : ℝ)..1, -w * (1 - u ^ 2) *
        Real.exp (-w * (1 - u ^ 2) * t) / (v + w * u ^ 2)) t := by
  unfold rationalLaplacePiece
  refine hasDerivAt_unitIntegral
    (F := fun y u : ℝ => Real.exp (-w * (1 - u ^ 2) * y) / (v + w * u ^ 2))
    (F' := fun y u : ℝ => -w * (1 - u ^ 2) *
      Real.exp (-w * (1 - u ^ 2) * y) / (v + w * u ^ 2)) ?_ ?_ ?_ t
  · apply Continuous.div (by fun_prop) (by fun_prop)
    intro p
    exact ne_of_gt (add_pos_of_pos_of_nonneg hv (mul_nonneg hw (sq_nonneg p.2)))
  · apply Continuous.div (by fun_prop) (by fun_prop)
    intro p
    exact ne_of_gt (add_pos_of_pos_of_nonneg hv (mul_nonneg hw (sq_nonneg p.2)))
  · intro y u
    exact (((hasDerivAt_id y).const_mul (-w * (1 - u ^ 2))).exp.div_const _).congr_deriv (by dsimp only [id_eq]; ring)

theorem rationalLaplacePiece_ode {v w : ℝ} (hv : 0 < v) (hw : 0 ≤ w) (t : ℝ) :
    deriv (rationalLaplacePiece v w) t + (v + w) * rationalLaplacePiece v w t =
      Real.exp (-w * t) * halfExpIntegral (w * t) := by
  have hA : Continuous (fun u : ℝ => Real.exp (-w * (1 - u ^ 2) * t) / (v + w * u ^ 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro u
    exact ne_of_gt (add_pos_of_pos_of_nonneg hv (mul_nonneg hw (sq_nonneg u)))
  have hB : Continuous (fun u : ℝ => -w * (1 - u ^ 2) *
      Real.exp (-w * (1 - u ^ 2) * t) / (v + w * u ^ 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro u
    exact ne_of_gt (add_pos_of_pos_of_nonneg hv (mul_nonneg hw (sq_nonneg u)))
  rw [(rationalLaplacePiece_hasDerivAt hv hw t).deriv]
  unfold rationalLaplacePiece halfExpIntegral
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
    (hB.intervalIntegrable 0 1) ((hA.const_mul _).intervalIntegrable 0 1),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  have hd : v + w * u ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hv (mul_nonneg hw (sq_nonneg u)))
  change -w * (1 - u ^ 2) * Real.exp (-w * (1 - u ^ 2) * t) / (v + w * u ^ 2) +
    (v + w) * (Real.exp (-w * (1 - u ^ 2) * t) / (v + w * u ^ 2)) =
      Real.exp (-w * t) * Real.exp (w * t * u ^ 2)
  rw [← Real.exp_add, show -w * t + w * t * u ^ 2 = -w * (1 - u ^ 2) * t by ring]
  field_simp
  ring

theorem rationalLaplaceKernel_hasDerivAt {v w : ℝ} (hv : 0 < v) (hw : 0 < w) (t : ℝ) :
    HasDerivAt (rationalLaplaceKernel v w)
      ((2 * Real.sqrt (v * w) / Real.pi) *
        (Real.exp (-w * t) * halfExpIntegral (w * t) +
          Real.exp (-v * t) * halfExpIntegral (v * t)) -
        (v + w) * rationalLaplaceKernel v w t) t := by
  have hd := ((rationalLaplacePiece_hasDerivAt hv hw.le t).differentiableAt.hasDerivAt.add
    (rationalLaplacePiece_hasDerivAt hw hv.le t).differentiableAt.hasDerivAt).const_mul
      (2 * Real.sqrt (v * w) / Real.pi)
  apply hd.congr_deriv
  unfold rationalLaplaceKernel
  linear_combination (2 * Real.sqrt (v * w) / Real.pi) * rationalLaplacePiece_ode hv hw.le t +
    (2 * Real.sqrt (v * w) / Real.pi) * rationalLaplacePiece_ode hw hv.le t

theorem halfExp_product_hasDerivAt (v w t : ℝ) :
    HasDerivAt (fun y => y * halfExpIntegral (v * y) * halfExpIntegral (w * y))
      ((Real.exp (v * t) * halfExpIntegral (w * t) +
        Real.exp (w * t) * halfExpIntegral (v * t)) / 2) t := by
  have hD := ((hasDerivAt_id t).mul
    ((halfExpIntegral_hasDerivAt (v * t)).differentiableAt.hasDerivAt.comp t
      ((hasDerivAt_id t).const_mul v))).mul
    ((halfExpIntegral_hasDerivAt (w * t)).differentiableAt.hasDerivAt.comp t
      ((hasDerivAt_id t).const_mul w))
  apply hD.congr_deriv
  dsimp only [Pi.mul_apply, Function.comp_apply, id_eq]
  linear_combination (halfExpIntegral (w * t) / 2) * halfExpIntegral_ode (v * t) +
    (halfExpIntegral (v * t) / 2) * halfExpIntegral_ode (w * t)

theorem halfProductKernel_hasDerivAt (v w t : ℝ) :
    HasDerivAt (halfProductKernel v w)
      ((2 * Real.sqrt (v * w) / Real.pi) *
        (Real.exp (-w * t) * halfExpIntegral (w * t) +
          Real.exp (-v * t) * halfExpIntegral (v * t)) -
        (v + w) * halfProductKernel v w t) t := by
  have he : halfProductKernel v w = fun y => Real.exp (-(v + w) * y) *
      (1 + (4 * Real.sqrt (v * w) / Real.pi) *
        (y * halfExpIntegral (v * y) * halfExpIntegral (w * y))) := by
    funext y
    unfold halfProductKernel
    ring
  rw [he]
  have hInner := HasDerivAt.const_add (1 : ℝ)
    ((halfExp_product_hasDerivAt v w t).const_mul (4 * Real.sqrt (v * w) / Real.pi))
  have hD := (((hasDerivAt_id t).const_mul (-(v + w))).exp).mul hInner
  apply hD.congr_deriv
  have hev : Real.exp (-(v + w) * t) * Real.exp (v * t) = Real.exp (-w * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hew : Real.exp (-(v + w) * t) * Real.exp (w * t) = Real.exp (-v * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only [Pi.mul_apply, Function.comp_apply, id_eq]
  linear_combination (2 * Real.sqrt (v * w) / Real.pi * halfExpIntegral (w * t)) * hev +
    (2 * Real.sqrt (v * w) / Real.pi * halfExpIntegral (v * t)) * hew

end MittagModulus
