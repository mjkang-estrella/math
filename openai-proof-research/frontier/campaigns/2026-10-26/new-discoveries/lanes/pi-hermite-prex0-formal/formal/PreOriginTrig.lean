import Mathlib

set_option autoImplicit false
set_option warningAsError true

namespace HermiteEnvelope

/-! # Pre-cutoff trigonometric bound for the Hermite odd bulk

Self-contained supporting lemma for the Guo--Liu Hermite envelope argument
(MathDB 346243), section "Bound before x0" of the parent proof: for `E ≥ 7`,
`0 ≤ u ≤ √2` and `c = √(1 - 2/E²)`,

    (1 - u²/E²) * sin (c*u)² ≤ (49/50) * (1 - 2/E²).

Route: `M(u) = (1 - u²/E²) sin²(cu)` is strictly increasing on `[0, √2]`
(derivative `2 sin(cu) [c(1-u²/E²) cos(cu) - (u/E²) sin(cu)] > 0`, using
`9/10 ≤ c ≤ 1`, `cu ≤ √2 < π/2`, `cos(cu) ≥ cos √2 ≥ 7/45` from a degree-6
alternating Taylor bound, and `sin(cu) ≤ 1`), hence `M(u) ≤ M(√2) =
(1 - 2/E²) sin²(c√2) ≤ (1 - 2/E²) sin²(√2) ≤ (1 - 2/E²) * 49/50`, the last
step via the degree-5 Taylor bound `sin √2 ≤ (7/10)√2`.

No hypotheses are assumed beyond `7 ≤ E`, `0 ≤ u`, `u ≤ √2`; all Taylor-type
inequalities are proved here from first principles (single-variable calculus
over the ordered reals). No `sorry`, `axiom`, `native_decide`, or unsafe
features. -/

/-- If `f` is differentiable, `deriv f ≥ 0` on `(0, ∞)` and `0 ≤ f 0`,
then `0 ≤ f t` for every `0 ≤ t`. -/
theorem ge_zero_of_deriv_nonneg {f : ℝ → ℝ} (hdiff : Differentiable ℝ f)
    (hd : ∀ t, 0 < t → 0 ≤ deriv f t) (h0 : 0 ≤ f 0) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ f t := by
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn
      (fun x hx => by
        rw [interior_Ici] at hx
        exact hd x hx)
  exact h0.trans (hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht)

/-- Degree-4 alternating Taylor **upper** bound for cosine, valid for `t ≥ 0`:
`cos t ≤ 1 - t²/2 + t⁴/24`.  (First rung of the Taylor ladder; the next two
rungs are `sin_le_poly5` and `cos_ge_poly6`.) -/
theorem cos_le_poly4 (t : ℝ) (ht : 0 ≤ t) : Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  -- G(s) = 1 - s²/2 + s⁴/24 - cos s has derivative sin s - s + s³/6 ≥ 0 by
  -- `Real.sin_ge_sub_cube`, and G(0) = 0.
  have hG' : ∀ s : ℝ, deriv (fun s : ℝ => 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s) s
      = Real.sin s - s + s ^ 3 / 6 := by
    intro s
    simp (disch := fun_prop)
    ring
  have hres := ge_zero_of_deriv_nonneg
    (f := fun s : ℝ => 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s)
    (by fun_prop)
    (fun s hs => by rw [hG' s]; linarith [Real.sin_ge_sub_cube hs.le])
    (by norm_num) t ht
  linarith

/-- Degree-5 alternating Taylor **upper** bound for sine, valid for `t ≥ 0`:
`sin t ≤ t - t³/6 + t⁵/120`. -/
theorem sin_le_poly5 (t : ℝ) (ht : 0 ≤ t) : Real.sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 120 := by
  -- F(s) = s - s³/6 + s⁵/120 - sin s has derivative 1 - s²/2 + s⁴/24 - cos s ≥ 0
  -- by `cos_le_poly4`, and F(0) = 0.
  have hF' : ∀ s : ℝ, deriv (fun s : ℝ => s - s ^ 3 / 6 + s ^ 5 / 120 - Real.sin s) s
      = 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s := by
    intro s
    simp (disch := fun_prop)
    ring
  have hres := ge_zero_of_deriv_nonneg
    (f := fun s : ℝ => s - s ^ 3 / 6 + s ^ 5 / 120 - Real.sin s)
    (by fun_prop)
    (fun s hs => by rw [hF' s]; linarith [cos_le_poly4 s (by linarith)])
    (by norm_num) t ht
  linarith

/-- Degree-6 alternating Taylor **lower** bound for cosine, valid for `t ≥ 0`:
`1 - t²/2 + t⁴/24 - t⁶/720 ≤ cos t`. -/
theorem cos_ge_poly6 (t : ℝ) (ht : 0 ≤ t) :
    1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 ≤ Real.cos t := by
  -- K(s) = cos s - (1 - s²/2 + s⁴/24 - s⁶/720) has derivative
  -- s - s³/6 + s⁵/120 - sin s ≥ 0 by `sin_le_poly5`, and K(0) = 0.
  have hK' : ∀ s : ℝ,
      deriv (fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) s
        = s - s ^ 3 / 6 + s ^ 5 / 120 - Real.sin s := by
    intro s
    simp (disch := fun_prop)
    ring
  have hres := ge_zero_of_deriv_nonneg
    (f := fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720))
    (by fun_prop)
    (fun s hs => by rw [hK' s]; linarith [sin_le_poly5 s (by linarith)])
    (by norm_num) t ht
  linarith

/-- Numerical consequence at `t = √2`: `cos √2 ≥ 7/45`. -/
theorem cos_sqrt2_ge_seven_45 : (7 : ℝ) / 45 ≤ Real.cos (Real.sqrt 2) := by
  have h := cos_ge_poly6 (Real.sqrt 2) (Real.sqrt_nonneg 2)
  have e2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e4 : (Real.sqrt 2) ^ 4 = 4 := by
    rw [show (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 from by ring, e2]
    norm_num
  have e6 : (Real.sqrt 2) ^ 6 = 8 := by
    rw [show (Real.sqrt 2) ^ 6 = ((Real.sqrt 2) ^ 2) ^ 3 from by ring, e2]
    norm_num
  rw [e2, e4, e6] at h
  norm_num at h
  exact h

/-- Numerical consequence at `t = √2`: `sin √2 ≤ (7/10)√2`. -/
theorem sin_sqrt2_le_seven_tenth_sqrt2 :
    Real.sin (Real.sqrt 2) ≤ (7 : ℝ) / 10 * Real.sqrt 2 := by
  have h := sin_le_poly5 (Real.sqrt 2) (Real.sqrt_nonneg 2)
  have e2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
    rw [show (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 from by ring,
      Real.sq_sqrt (by norm_num)]
  have e5 : (Real.sqrt 2) ^ 5 = 4 * Real.sqrt 2 := by
    rw [show (Real.sqrt 2) ^ 5 = ((Real.sqrt 2) ^ 2) ^ 2 * Real.sqrt 2 from by ring, e2]
    norm_num
  rw [e3, e5] at h
  linarith

/-- **Main pre-cutoff trigonometric bound.**  For `E ≥ 7`, `0 ≤ u ≤ √2` and
`c = √(1 - 2/E²)`:
`(1 - u²/E²) * sin (c*u)² ≤ (49/50) * (1 - 2/E²)`. -/
theorem preX0_sin_sq_bound (E : ℝ) (hE : 7 ≤ E) (u : ℝ) (hu : 0 ≤ u)
    (hu2 : u ≤ Real.sqrt 2) :
    (1 - u ^ 2 / E ^ 2) * Real.sin (Real.sqrt (1 - 2 / E ^ 2) * u) ^ 2
      ≤ (49 / 50) * (1 - 2 / E ^ 2) := by
  set c : ℝ := Real.sqrt (1 - 2 / E ^ 2) with hcdef
  rw [show Real.sin (c * u) ^ 2 = Real.sin (c * u) * Real.sin (c * u) from pow_two _]
  -- basic facts about E and c
  have hE0 : (0 : ℝ) < E := by linarith
  have hE2 : (49 : ℝ) ≤ E ^ 2 := by nlinarith
  have h47 : (47 : ℝ) / 49 ≤ 1 - 2 / E ^ 2 := by
    have h2 : (2 : ℝ) / E ^ 2 ≤ 2 / 49 := by
      rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
      linarith
    linarith
  have hc0 : 0 ≤ c := by rw [hcdef]; exact Real.sqrt_nonneg _
  have hc1 : c ≤ 1 := by
    rw [hcdef, ← Real.sqrt_one]
    refine Real.sqrt_le_sqrt ?_
    have : (0 : ℝ) ≤ 2 / E ^ 2 := div_nonneg (by norm_num) (sq_nonneg E)
    linarith
  have hc9 : 9 / 10 ≤ c := by
    have h81 : (81 : ℝ) / 100 ≤ 1 - 2 / E ^ 2 := by
      have h2 : (2 : ℝ) / E ^ 2 ≤ 2 / 49 := by
        rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
        linarith
      norm_num
      linarith
    have key : ((9 : ℝ) / 10) ^ 2 ≤ 1 - 2 / E ^ 2 := by
      have hsq : ((9 : ℝ) / 10) ^ 2 = 81 / 100 := by norm_num
      rw [hsq]; exact h81
    have hs := Real.sqrt_le_sqrt key
    rw [Real.sqrt_sq (show (0 : ℝ) ≤ 9 / 10 by norm_num)] at hs
    rwa [← hcdef] at hs
  have hcv2 : c * Real.sqrt 2 ≤ Real.sqrt 2 := by
    calc c * Real.sqrt 2 ≤ 1 * Real.sqrt 2 := mul_le_mul_of_nonneg_right hc1 (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 := one_mul _
  -- π bounds: √2 < π/2
  have hhalf : Real.sqrt 2 < Real.pi / 2 := by
    have h1 : Real.sqrt 2 ≤ 3 / 2 := by
      have h := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ ((3 : ℝ) / 2) ^ 2 by norm_num)
      rwa [Real.sqrt_sq (show (0 : ℝ) ≤ 3 / 2 by norm_num)] at h
    linarith [Real.pi_gt_three]
  -- derivative of M
  have hF' : ∀ v : ℝ,
      deriv (fun w : ℝ => (1 - w ^ 2 / E ^ 2) * (Real.sin (c * w) * Real.sin (c * w))) v
        = 2 * Real.sin (c * v) *
          (c * (1 - v ^ 2 / E ^ 2) * Real.cos (c * v) - v / E ^ 2 * Real.sin (c * v)) := by
    intro v
    simp (disch := fun_prop)
    ring
  -- derivative positivity on (0, √2)
  have hFpos : ∀ v ∈ Set.Ioo 0 (Real.sqrt 2),
      0 < deriv (fun w : ℝ => (1 - w ^ 2 / E ^ 2) * (Real.sin (c * w) * Real.sin (c * w))) v := by
    intro v hv
    have hv0 : 0 < v := hv.1
    have hv2 : v ≤ Real.sqrt 2 := hv.2.le
    have hvle : v ≤ 2 := by
      have h := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (2 : ℝ) ^ 2 by norm_num)
      rw [Real.sqrt_sq (by norm_num)] at h
      exact le_trans hv2 h
    have hvsq : v ^ 2 ≤ 2 := by
      have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ v by linarith) hv2 2
      rwa [Real.sq_sqrt (by norm_num)] at h
    have hcv0 : 0 < c * v := mul_pos (by linarith [hc9]) hv0
    have hcvnn : 0 ≤ c * v := mul_nonneg hc0 hv0.le
    have hcuv : c * v ≤ Real.sqrt 2 := by
      calc c * v ≤ 1 * v := mul_le_mul_of_nonneg_right hc1 (by linarith)
        _ = v := one_mul v
        _ ≤ Real.sqrt 2 := hv2
    have hsinpos : 0 < Real.sin (c * v) :=
      Real.sin_pos_of_pos_of_lt_pi hcv0 (by linarith [hcuv, hhalf, Real.pi_pos])
    have hcos_ge : (7 : ℝ) / 45 ≤ Real.cos (c * v) := by
      have h1 : Real.cos (Real.sqrt 2) ≤ Real.cos (c * v) :=
        Real.cos_le_cos_of_nonneg_of_le_pi hcvnn
          (show Real.sqrt 2 ≤ Real.pi by linarith [hhalf, Real.pi_pos]) hcuv
      exact le_trans cos_sqrt2_ge_seven_45 h1
    have hA47 : (47 : ℝ) / 49 ≤ 1 - v ^ 2 / E ^ 2 := by
      have h2 : (v : ℝ) ^ 2 / E ^ 2 ≤ 2 / 49 := by
        rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
        linarith
      linarith [h47]
    have hterm1 : (329 : ℝ) / 2450 ≤ c * (1 - v ^ 2 / E ^ 2) * Real.cos (c * v) := by
      have hnn : (0 : ℝ) ≤ 1 - v ^ 2 / E ^ 2 := by linarith [hA47]
      have h1 : (9 : ℝ) / 10 * (1 - v ^ 2 / E ^ 2) ≤ c * (1 - v ^ 2 / E ^ 2) :=
        mul_le_mul_of_nonneg_right hc9 hnn
      have h2 : (9 : ℝ) / 10 * (47 / 49) ≤ (9 : ℝ) / 10 * (1 - v ^ 2 / E ^ 2) :=
        mul_le_mul_of_nonneg_left hA47 (by norm_num)
      have h3 : (9 : ℝ) / 10 * (1 - v ^ 2 / E ^ 2) * (7 / 45)
          ≤ c * (1 - v ^ 2 / E ^ 2) * (7 / 45) :=
        mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ (7 : ℝ) / 45)
      have hnn9 : (0 : ℝ) ≤ (9 : ℝ) / 10 * (1 - v ^ 2 / E ^ 2) :=
        mul_nonneg (by norm_num) hnn
      have h4c : (9 : ℝ) / 10 * (1 - v ^ 2 / E ^ 2) * (7 / 45)
          ≤ (9 : ℝ) / 10 * (1 - v ^ 2 / E ^ 2) * Real.cos (c * v) :=
        mul_le_mul_of_nonneg_left hcos_ge hnn9
      have hnn2 : (0 : ℝ) ≤ Real.cos (c * v) := le_trans (by norm_num) hcos_ge
      calc (329 : ℝ) / 2450 = (9 : ℝ) / 10 * (47 / 49) * (7 / 45) := by norm_num
        _ ≤ (9 : ℝ) / 10 * (1 - v ^ 2 / E ^ 2) * (7 / 45) :=
              mul_le_mul_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ (7 : ℝ) / 45)
        _ ≤ (9 : ℝ) / 10 * (1 - v ^ 2 / E ^ 2) * Real.cos (c * v) := h4c
        _ ≤ c * (1 - v ^ 2 / E ^ 2) * Real.cos (c * v) :=
              mul_le_mul_of_nonneg_right h1 hnn2
    have hterm2 : (v : ℝ) / E ^ 2 * Real.sin (c * v) ≤ 2 / 49 := by
      have hve : (v : ℝ) / E ^ 2 ≤ 2 / 49 := by
        rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
        linarith
      have hsin_nn : 0 ≤ Real.sin (c * v) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hcvnn
          (show c * v ≤ Real.pi by linarith [hcuv, hhalf, Real.pi_pos])
      exact (mul_le_mul hve (Real.sin_le_one _) hsin_nn (by norm_num)).trans (by norm_num)
    have hbr : 0 < c * (1 - v ^ 2 / E ^ 2) * Real.cos (c * v)
        - v / E ^ 2 * Real.sin (c * v) := by
      have h3 : (2 : ℝ) / 49 < 329 / 2450 := by norm_num
      linarith
    rw [hF' v]
    exact mul_pos (mul_pos (by norm_num) hsinpos) hbr
  -- strict monotonicity of M on [0, √2]
  have hmono : StrictMonoOn
      (fun w : ℝ => (1 - w ^ 2 / E ^ 2) * (Real.sin (c * w) * Real.sin (c * w)))
      (Set.Icc 0 (Real.sqrt 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · have hdiffF : Differentiable ℝ
          (fun w : ℝ => (1 - w ^ 2 / E ^ 2) * (Real.sin (c * w) * Real.sin (c * w))) := by
        intro w
        have h1 : HasDerivAt (fun w : ℝ => 1 - w ^ 2 / E ^ 2) (-(2 * w / E ^ 2)) w := by
          simpa using (hasDerivAt_pow 2 w).div_const (E ^ 2) |>.const_sub 1
        have hc : HasDerivAt (fun w : ℝ => c * w) c w := by
          simpa using (hasDerivAt_id w).const_mul c
        have h2 := (Real.hasDerivAt_sin (c * w)).comp w hc
        exact (h1.mul (h2.mul h2)).differentiableAt
      exact hdiffF.continuous.continuousOn
    · intro v hv
      rw [interior_Icc] at hv
      exact hFpos v hv
  -- value at √2
  have hSQ2 : (1 - (Real.sqrt 2) ^ 2 / E ^ 2)
        * (Real.sin (c * Real.sqrt 2) * Real.sin (c * Real.sqrt 2))
      ≤ (49 : ℝ) / 50 * (1 - 2 / E ^ 2) := by
    have hsin_c : Real.sin (c * Real.sqrt 2) ≤ Real.sin (Real.sqrt 2) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [mul_nonneg hc0 (Real.sqrt_nonneg 2), Real.pi_pos])
        hhalf.le
        hcv2
    have hsin2 : Real.sin (c * Real.sqrt 2) ≤ (7 : ℝ) / 10 * Real.sqrt 2 :=
      le_trans hsin_c sin_sqrt2_le_seven_tenth_sqrt2
    have hsin_nn : 0 ≤ Real.sin (c * Real.sqrt 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [mul_nonneg hc0 (Real.sqrt_nonneg 2)])
        (show c * Real.sqrt 2 ≤ Real.pi by linarith [hcv2, hhalf, Real.pi_pos])
    have h49 : ((7 : ℝ) / 10 * Real.sqrt 2) ^ 2 = 49 / 50 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have h5 := pow_le_pow_left₀ hsin_nn hsin2 2
    rw [h49, pow_two] at h5
    rw [Real.sq_sqrt (by norm_num)]
    exact (mul_le_mul_of_nonneg_left h5
      (by linarith : (0 : ℝ) ≤ 1 - 2 / E ^ 2)).trans (by linarith)
  -- finish
  rcases eq_or_lt_of_le hu with rfl | hvu
  · have h0 : (1 - (0 : ℝ) ^ 2 / E ^ 2) * (Real.sin (c * 0) * Real.sin (c * 0)) = 0 := by
      simp
    rw [h0]
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 49 / 50) (by linarith [h47])
  rcases lt_or_eq_of_le hu2 with hvlt | rfl
  · exact le_of_lt (hmono (Set.mem_Icc.2 ⟨hu, hu2⟩)
      (Set.mem_Icc.2 ⟨Real.sqrt_nonneg 2, le_refl _⟩) hvlt) |>.trans hSQ2
  · exact hSQ2

end HermiteEnvelope
