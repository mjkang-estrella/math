import SourceDefs

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option warningAsError true

open scoped Interval
open Set MeasureTheory intervalIntegral

noncomputable section

namespace HermiteEnvelope

variable {E A : ℝ} {f g : ℝ → ℝ}

/-! ## Regularity derived from the first-order ODE system -/

/-- The ODE system makes `f` continuous. -/
theorem odesys_continuous_f (hf : ∀ t, HasDerivAt f (g t) t) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (hf x).continuousAt

/-- The ODE system makes `g` continuous. -/
theorem odesys_continuous_g (hg : ∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t) : Continuous g :=
  continuous_iff_continuousAt.2 fun x => (hg x).continuousAt

/-! ## Numerical facts about `√2` and `π` -/

theorem comparison_sqrt2_lt_pi : Real.sqrt 2 < Real.pi :=
  lt_trans (by
    calc Real.sqrt 2 < Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 3 := by norm_num) Real.pi_gt_three

theorem comparison_sqrt2_le_pi_div_two : Real.sqrt 2 ≤ Real.pi / 2 := by
  have h1 : Real.sqrt 2 ≤ 3 / 2 := by
    calc Real.sqrt 2 ≤ Real.sqrt (9 / 4) := Real.sqrt_le_sqrt (by norm_num)
      _ = 3 / 2 := by norm_num
  have h2 : 3 / 2 ≤ Real.pi / 2 :=
    (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 (le_of_lt Real.pi_gt_three)
  linarith

/-! ## The Duhamel (variation-of-constants) identity

For the system `f' = g`, `g' = (t^2 - E) * f` with `f 0 = 0`, `g 0 = A`, the
Wronskian combination `W(t) = sin(√q(x - t)) g(t) + √q cos(√q(x - t)) f(t)`
has derivative `(t^2 - E + q) f(t) sin(√q (x - t))`; the fundamental theorem of
calculus on `[0, x]` then gives the exact variation-of-constants formula.  No
positivity, sign, or size hypothesis on `f` is used anywhere in this section.
-/

/-- Pointwise derivative of the Wronskian combination (the key Duhamel kernel). -/
theorem comparison_wronskian_deriv (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t) (q x t : ℝ) (hq : 0 ≤ q) :
    HasDerivAt (fun s => Real.sin (Real.sqrt q * (x - s)) * g s +
        Real.sqrt q * Real.cos (Real.sqrt q * (x - s)) * f s)
      ((t ^ 2 - E + q) * f t * Real.sin (Real.sqrt q * (x - t))) t := by
  have h1 : HasDerivAt (fun s : ℝ => x - s) (-1) t := (hasDerivAt_id t).const_sub x
  have hu : HasDerivAt (fun s : ℝ => Real.sqrt q * (x - s)) (-Real.sqrt q) t := by
    have h2 := h1.const_mul (Real.sqrt q)
    have hv : (Real.sqrt q * -1 : ℝ) = -Real.sqrt q := by ring
    rwa [hv] at h2
  have hS : HasDerivAt (fun s => Real.sin (Real.sqrt q * (x - s)))
      (Real.cos (Real.sqrt q * (x - t)) * -Real.sqrt q) t := by
    refine HasDerivAt.comp (x := t) (h := fun s : ℝ => Real.sqrt q * (x - s))
      (h₂ := Real.sin) (h₂' := Real.cos (Real.sqrt q * (x - t))) ?_ hu
    exact Real.hasDerivAt_sin (Real.sqrt q * (x - t))
  have hCcos : HasDerivAt (fun s => Real.cos (Real.sqrt q * (x - s)))
      (-Real.sin (Real.sqrt q * (x - t)) * -Real.sqrt q) t := by
    refine HasDerivAt.comp (x := t) (h := fun s : ℝ => Real.sqrt q * (x - s))
      (h₂ := Real.cos) (h₂' := -Real.sin (Real.sqrt q * (x - t))) ?_ hu
    exact Real.hasDerivAt_cos (Real.sqrt q * (x - t))
  have hC : HasDerivAt (fun s => Real.sqrt q * Real.cos (Real.sqrt q * (x - s)))
      (q * Real.sin (Real.sqrt q * (x - t))) t := by
    have h2 := hCcos.const_mul (Real.sqrt q)
    have hv : Real.sqrt q * (-Real.sin (Real.sqrt q * (x - t)) * -Real.sqrt q) =
        q * Real.sin (Real.sqrt q * (x - t)) := by
      have hqq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq
      calc Real.sqrt q * (-Real.sin (Real.sqrt q * (x - t)) * -Real.sqrt q)
          = Real.sqrt q * Real.sqrt q * Real.sin (Real.sqrt q * (x - t)) := by ring
        _ = q * Real.sin (Real.sqrt q * (x - t)) := by rw [hqq]
    rwa [hv] at h2
  convert ((hS.mul (hg t)).add (hC.mul (hf t))) using 1
  ring

/-- Exact variation-of-constants (Duhamel) identity for the generic ODE system,
proved by the Wronskian computation and the fundamental theorem of calculus.
It holds for every real `x`; no hypothesis on the sign of `f` is involved. -/
theorem duhamel_identity (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t)
    (hf0 : f 0 = 0) (hg0 : g 0 = A) (q : ℝ) (hq : 0 ≤ q) (x : ℝ) :
    Real.sqrt q * f x = A * Real.sin (Real.sqrt q * x) +
      ∫ s in (0 : ℝ)..x, (s ^ 2 - E + q) * f s * Real.sin (Real.sqrt q * (x - s)) := by
  have hfc : Continuous f := odesys_continuous_f hf
  have hgc : Continuous g := odesys_continuous_g hg
  have hint : IntervalIntegrable
      (fun s => (s ^ 2 - E + q) * f s * Real.sin (Real.sqrt q * (x - s))) volume 0 x := by
    exact (by fun_prop : Continuous
      (fun s => (s ^ 2 - E + q) * f s * Real.sin (Real.sqrt q * (x - s)))).intervalIntegrable 0 x
  have hFTC := integral_eq_sub_of_hasDerivAt
    (f := fun s => Real.sin (Real.sqrt q * (x - s)) * g s +
      Real.sqrt q * Real.cos (Real.sqrt q * (x - s)) * f s)
    (f' := fun s => (s ^ 2 - E + q) * f s * Real.sin (Real.sqrt q * (x - s)))
    (fun t _ => comparison_wronskian_deriv hf hg q x t hq) hint
  have hWx : Real.sin (Real.sqrt q * (x - x)) * g x +
      Real.sqrt q * Real.cos (Real.sqrt q * (x - x)) * f x = Real.sqrt q * f x := by
    simp
  have hW0 : Real.sin (Real.sqrt q * (x - 0)) * g 0 +
      Real.sqrt q * Real.cos (Real.sqrt q * (x - 0)) * f 0 =
      A * Real.sin (Real.sqrt q * x) := by
    rw [sub_zero, hg0, hf0]
    ring
  rw [hWx, hW0] at hFTC
  linarith

/-! ## Elementary one-variable estimates used by the comparison -/

/-- `sin t ≤ t` for `t ≥ 0`, via the monotone function `t - sin t`. -/
theorem comparison_sin_le_self_of_nonneg {t : ℝ} (ht : 0 ≤ t) : Real.sin t ≤ t := by
  have hmono : MonotoneOn (fun s : ℝ => s - Real.sin s) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) ?_ ?_ ?_
    · exact (by fun_prop : Continuous (fun s : ℝ => s - Real.sin s)).continuousOn
    · intro s _
      exact ((hasDerivAt_id s).sub (Real.hasDerivAt_sin s)).differentiableAt.differentiableWithinAt
    · intro s _
      have hd : deriv (fun s : ℝ => s - Real.sin s) s = 1 - Real.cos s :=
        ((hasDerivAt_id s).sub (Real.hasDerivAt_sin s)).deriv
      rw [hd]
      linarith [Real.cos_le_one s]
  have h0 := hmono (mem_Ici.2 (le_refl 0)) (mem_Ici.2 ht) ht
  simpa using h0

/-- `2 cos t - 2 + t² ≥ 0` for `t ≥ 0` (i.e. `cos t ≥ 1 - t²/2`), via the
monotone function `2 cos t - 2 + t²` whose derivative is `2 (t - sin t) ≥ 0`. -/
theorem comparison_two_cos_ge (t : ℝ) (ht : 0 ≤ t) : 0 ≤ 2 * Real.cos t - 2 + t ^ 2 := by
  have hpow : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := fun s => by
    simpa using hasDerivAt_pow 2 s
  have hcos2 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 2 * Real.cos s) (-2 * Real.sin s) s :=
    fun s => by
      refine ((Real.hasDerivAt_cos s).const_mul 2).congr_deriv ?_
      ring
  have hmono : MonotoneOn (fun s : ℝ => 2 * Real.cos s - 2 + s ^ 2) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) ?_ ?_ ?_
    · exact (by fun_prop : Continuous (fun s : ℝ => 2 * Real.cos s - 2 + s ^ 2)).continuousOn
    · intro s _
      exact ((((Real.hasDerivAt_cos s).const_mul 2).sub
        (hasDerivAt_const s 2)).add (hpow s)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hd : deriv (fun s : ℝ => 2 * Real.cos s - 2 + s ^ 2) s =
          -2 * Real.sin s + 2 * s := by
        have h2 : HasDerivAt (fun s : ℝ => 2 * Real.cos s - 2 + s ^ 2)
            (-2 * Real.sin s + 2 * s) s :=
          HasDerivAt.fun_add
            (((hcos2 s).fun_sub (hasDerivAt_const s 2)).congr_deriv (by ring)) (hpow s)
        exact h2.deriv
      rw [hd]
      have hs' : s ∈ Ioi (0 : ℝ) := by
        rw [← interior_Ici]; exact hs
      have hkey : 0 ≤ 2 * (s - Real.sin s) := by
        refine mul_nonneg zero_le_two ?_
        exact sub_nonneg.2 (comparison_sin_le_self_of_nonneg hs'.le)
      linarith
  have h0 := hmono (mem_Ici.2 (le_refl 0)) (mem_Ici.2 ht) ht
  simpa using h0

/-- Taylor lower bound `x - x³/6 ≤ sin x` for `x ≥ 0`, from the exact integral
of `cos` and the quadratic lower bound for `cos`. -/
theorem comparison_sin_ge_x_sub_cube_div_six {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ Real.sin x := by
  have hcos : Continuous (Real.cos : ℝ → ℝ) := by fun_prop
  have hintcos : IntervalIntegrable (Real.cos : ℝ → ℝ) volume 0 x := hcos.intervalIntegrable 0 x
  have h1 : ∫ s in (0 : ℝ)..x, Real.cos s = Real.sin x :=
    (integral_eq_sub_of_hasDerivAt (f := Real.sin) (f' := Real.cos)
      (fun s _ => Real.hasDerivAt_sin s) hintcos).trans (by simp)
  have h2 : (∫ s in (0 : ℝ)..x, (2 - s ^ 2)) ≤ 2 * ∫ s in (0 : ℝ)..x, Real.cos s := by
    have hpt : ∀ s ∈ Icc 0 x, (2 - s ^ 2) ≤ 2 * Real.cos s := by
      intro s hs
      have := comparison_two_cos_ge s hs.1
      linarith
    have hint1 : IntervalIntegrable (fun s : ℝ => 2 - s ^ 2) volume 0 x :=
      (by fun_prop : Continuous (fun s : ℝ => 2 - s ^ 2)).intervalIntegrable 0 x
    have hint2 : IntervalIntegrable (fun s : ℝ => 2 * Real.cos s) volume 0 x :=
      (by fun_prop : Continuous (fun s : ℝ => 2 * Real.cos s)).intervalIntegrable 0 x
    have hcos2 : ∫ s in (0 : ℝ)..x, (2 * Real.cos s) = 2 * ∫ s in (0 : ℝ)..x, Real.cos s := by
      rw [intervalIntegral.integral_const_mul]
    calc ∫ s in (0 : ℝ)..x, (2 - s ^ 2)
        ≤ ∫ s in (0 : ℝ)..x, (2 * Real.cos s) :=
          intervalIntegral.integral_mono_on hx hint1 hint2 hpt
      _ = 2 * ∫ s in (0 : ℝ)..x, Real.cos s := hcos2
  have h3 : ∫ s in (0 : ℝ)..x, (2 - s ^ 2) = 2 * x - x ^ 3 / 3 := by
    rw [intervalIntegral.integral_sub
      (((by fun_prop : Continuous (fun _ : ℝ => (2 : ℝ)))).intervalIntegrable 0 x)
      (((by fun_prop : Continuous (fun s : ℝ => s ^ 2))).intervalIntegrable 0 x),
      intervalIntegral.integral_const, integral_pow]
    ring
  have hsin2 : 2 * Real.sin x ≥ 2 * x - x ^ 3 / 3 := by
    calc 2 * Real.sin x = 2 * ∫ s in (0 : ℝ)..x, Real.cos s := by rw [h1]
      _ ≥ ∫ s in (0 : ℝ)..x, (2 - s ^ 2) := by linarith
      _ = 2 * x - x ^ 3 / 3 := h3
  linarith

theorem comparison_sin_one_ge_five_six : (5 : ℝ) / 6 ≤ Real.sin 1 := by
  have h := comparison_sin_ge_x_sub_cube_div_six (x := 1) (by norm_num)
  norm_num at h
  exact h

/-! ## Positivity of `f` on the short interval `[0, √(2/E)]`

Near `0` this is immediate from `g 0 = A > 0`.  Beyond that, a genuine first
zero `z ≤ √(2/E)` is excluded by the Duhamel identity: the integral term is
nonnegative because `f > 0` on `(0, z)` (minimality of `z`) and the sine kernel
`sin(√E (z - s))` is nonnegative since `√E z ≤ √2 < π`.
-/

/-- `√E * w ≤ √2` whenever `w ≤ √(2/E)` and `E ≥ 7`. -/
theorem comparison_sqrtE_mul_short_le_sqrt2 (hE : 7 ≤ E) {w : ℝ} (hw : w ≤ Real.sqrt (2 / E)) :
    Real.sqrt E * w ≤ Real.sqrt 2 := by
  have hEpos : 0 < E := by linarith
  calc Real.sqrt E * w ≤ Real.sqrt E * Real.sqrt (2 / E) :=
          mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg E)
    _ = Real.sqrt 2 := by
      have hmul : E * (2 / E) = 2 := by field_simp
      rw [← Real.sqrt_mul hEpos.le, hmul]

/-- `√(E - 2/E) * w ≤ √2` whenever `w ≤ √(2/E)` and `E ≥ 7`. -/
theorem comparison_sqrtq0_mul_short_le_sqrt2 (hE : 7 ≤ E) {w : ℝ} (hw : w ≤ Real.sqrt (2 / E))
    (hw0 : 0 ≤ w) :
    Real.sqrt (E - 2 / E) * w ≤ Real.sqrt 2 := by
  have hEpos : 0 < E := by linarith
  have hle : E - 2 / E ≤ E := by
    have h2E : 2 / E ≤ 2 / 7 := (div_le_div_iff₀ (by linarith) (by norm_num)).2 (by linarith)
    have h2Epos : 0 < 2 / E := div_pos two_pos (by linarith)
    linarith
  calc Real.sqrt (E - 2 / E) * w ≤ Real.sqrt E * w :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hle) hw0
    _ ≤ Real.sqrt 2 := comparison_sqrtE_mul_short_le_sqrt2 hE hw

/-- `q₀ = E - 2/E` is positive for `E ≥ 7`. -/
theorem comparison_q0_pos (hE : 7 ≤ E) : 0 < E - 2 / E := by
  have hEpos : 0 < E := by linarith
  have h2E : 2 / E ≤ 2 / 7 := (div_le_div_iff₀ (by linarith) (by norm_num)).2 (by linarith)
  have h2Epos : 0 < 2 / E := div_pos two_pos hEpos
  linarith

/-- Positivity very near `0` from `g 0 = A > 0`. -/
theorem odesys_pos_near_zero (hA : 0 < A) (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t) (hf0 : f 0 = 0) (hg0 : g 0 = A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → 0 < f t := by
  have hnb : ∀ᶠ y in nhds (0 : ℝ), g y ∈ Ioi (A / 2) := by
    have hmem : Ioi (A / 2) ∈ nhds (g 0) := by
      rw [hg0]
      exact Ioi_mem_nhds (by linarith)
    exact (hg 0).continuousAt.preimage_mem_nhds hmem
  obtain ⟨δ, hδ, hsub⟩ := Metric.nhds_basis_ball.mem_iff.1 hnb
  refine ⟨δ, hδ, fun t ht0 htd => ?_⟩
  have hgs : ∀ s, |s| < δ → A / 2 < g s := by
    intro s habs
    have : g s ∈ Ioi (A / 2) := hsub (mem_ball_zero_iff.2 habs)
    exact this
  have hmono : StrictMonoOn f (Icc 0 δ) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) δ) ?_ ?_
    · exact (odesys_continuous_f hf).continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      have hd : deriv f s = g s := (hf s).deriv
      rw [hd]
      have habs : |s| < δ := abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
      exact lt_trans (show (0 : ℝ) < A / 2 by linarith) (hgs s habs)
  have hlt := hmono (mem_Icc.2 ⟨le_refl 0, le_of_lt hδ⟩)
    (mem_Icc.2 ⟨le_of_lt ht0, le_of_lt htd⟩) ht0
  have : f 0 < f t := hlt
  rw [hf0] at this
  linarith

/-- **Main positivity lemma.** `f` is strictly positive on the half-open short
interval `(0, √(2/E)]`.  The proof is the genuine first-zero contradiction:
if the set of nonpositive points in `[δ, x0]` had a least element `z`, the
Duhamel identity at `z` would force `f z > 0`. -/
theorem odesys_pos (hE : 7 ≤ E) (hA : 0 < A) (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t) (hf0 : f 0 = 0) (hg0 : g 0 = A) :
    ∀ t, 0 < t → t ≤ Real.sqrt (2 / E) → 0 < f t := by
  have hEpos : 0 < E := by linarith
  set x0 := Real.sqrt (2 / E) with hx0def
  have hx0pos : 0 < x0 := Real.sqrt_pos.2 (div_pos two_pos hEpos)
  obtain ⟨δ, hδ, hnear⟩ := odesys_pos_near_zero hA hf hg hf0 hg0
  intro t ht0 htx
  by_contra hcon
  -- the bad point sits at or beyond δ
  have htδ : δ ≤ t := by
    rcases le_or_gt δ t with h | h
    · exact h
    · exact absurd (hnear t ht0 h) (by linarith)
  -- the closed bad set and its least element
  have hfc : Continuous f := odesys_continuous_f hf
  set S : Set ℝ := {x : ℝ | δ ≤ x ∧ x ≤ x0 ∧ f x ≤ 0} with hSdef
  have hSne : S.Nonempty := ⟨t, htδ, htx, le_of_not_gt hcon⟩
  have hSclosed : IsClosed S := by
    have hSS : S = Icc δ x0 ∩ f ⁻¹' (Iic 0) := by
      ext x
      simp [hSdef, mem_inter_iff, mem_preimage, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    rw [hSS]
    exact isClosed_Icc.inter (IsClosed.preimage hfc isClosed_Iic)
  have hScompact : IsCompact S := by
    refine IsCompact.of_isClosed_subset (s := Icc (0 : ℝ) x0) isCompact_Icc hSclosed ?_
    intro x hx
    exact ⟨hδ.le.trans hx.1, hx.2.1⟩
  obtain ⟨z, hzS, hzmin⟩ := hScompact.exists_isMinOn hSne continuousOn_id
  have hzle : ∀ y ∈ S, z ≤ y := isMinOn_iff.1 hzmin
  have hzx : z ≤ Real.sqrt (2 / E) := by
    have h2 : z ≤ x0 := hzS.2.1
    rwa [hx0def] at h2
  have hfz0 : f z ≤ 0 := hzS.2.2
  have hzpos : 0 < z := lt_of_lt_of_le hδ hzS.1
  -- f is strictly positive strictly below z
  have hposz : ∀ y, 0 < y → y < z → 0 < f y := by
    intro y hy0 hyz
    rcases le_or_gt δ y with hyδ | hyd
    · have hyx0 : y ≤ x0 := le_trans (le_of_lt hyz) hzx
      have hynS : y ∉ S := fun hm => lt_irrefl y (lt_of_lt_of_le hyz (hzle y hm))
      exact not_le.1 fun hm => hynS ⟨hyδ, hyx0, hm⟩
    · exact hnear y hy0 hyd
  -- Duhamel at z with parameter q = E: the integral term is nonnegative
  have hd : Real.sqrt E * f z = A * Real.sin (Real.sqrt E * z) +
      ∫ s in (0 : ℝ)..z, (s ^ 2 - E + E) * f s * Real.sin (Real.sqrt E * (z - s)) :=
    duhamel_identity hf hg hf0 hg0 E (le_of_lt hEpos) z
  have hinteg : 0 ≤ ∫ s in (0 : ℝ)..z, (s ^ 2 - E + E) * f s *
      Real.sin (Real.sqrt E * (z - s)) := by
    refine intervalIntegral.integral_nonneg hzpos.le (fun s hs => ?_)
    have hsz : s ≤ z := hs.2
    have hsin : 0 ≤ Real.sin (Real.sqrt E * (z - s)) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (Real.sqrt_nonneg E) ?_) ?_
      · exact sub_nonneg.2 hsz
      · exact le_trans (comparison_sqrtE_mul_short_le_sqrt2 hE
          (le_trans (sub_le_self z hs.1) hzx)) comparison_sqrt2_lt_pi.le
    have hprod : (s ^ 2 - E + E) * f s * Real.sin (Real.sqrt E * (z - s)) =
        s ^ 2 * f s * Real.sin (Real.sqrt E * (z - s)) := by ring
    rw [hprod]
    rcases eq_or_lt_of_le hsz with hEq | hLt
    · subst hEq; simp
    · have hs0 : 0 ≤ s := hs.1
      have hfs : 0 ≤ f s := by
        rcases eq_or_lt_of_le hs0 with h0 | h0
        · subst h0; simp [hf0]
        · exact le_of_lt (hposz s h0 (by linarith))
      exact mul_nonneg (mul_nonneg (sq_nonneg s) hfs) hsin
  -- hence f z > 0, contradicting f z ≤ 0
  have hsinz : 0 < Real.sin (Real.sqrt E * z) := by
    refine Real.sin_pos_of_pos_of_lt_pi (mul_pos (Real.sqrt_pos.2 hEpos) hzpos) ?_
    exact lt_of_le_of_lt (comparison_sqrtE_mul_short_le_sqrt2 hE hzx) comparison_sqrt2_lt_pi
  have h1 : A * Real.sin (Real.sqrt E * z) ≤ Real.sqrt E * f z := by linarith
  have h2 : (A * Real.sin (Real.sqrt E * z)) / Real.sqrt E ≤ f z :=
    (div_le_iff₀ (Real.sqrt_pos.2 hEpos)).2 (by linarith [h1, mul_comm (f z) (Real.sqrt E)])
  have hfz : 0 < f z :=
    lt_of_lt_of_le (div_pos (mul_pos hA hsinz) (Real.sqrt_pos.2 hEpos)) h2
  exact absurd hfz (not_lt.2 hfz0)

/-- On `[0, √(2/E)]` the function `f` is nonnegative (from `odesys_pos`). -/
theorem odesys_nonneg (hE : 7 ≤ E) (hA : 0 < A) (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t) (hf0 : f 0 = 0) (hg0 : g 0 = A)
    (t : ℝ) (ht0 : 0 ≤ t) (htx : t ≤ Real.sqrt (2 / E)) : 0 ≤ f t := by
  rcases eq_or_lt_of_le ht0 with h | h
  · subst h; rw [hf0]
  · exact le_of_lt (odesys_pos hE hA hf hg hf0 hg0 t h htx)

/-! ## Positivity helpers for the two Duhamel kernels -/

/-- The lower-kernel integral `∫₀^z s² f(s) sin(√E (z-s)) ds` is nonnegative
whenever `f ≥ 0` on `[0, z]` and `z ≤ √(2/E)`. -/
theorem comparison_lower_integral_nonneg (hE : 7 ≤ E) (hnn : ∀ t, 0 ≤ t →
    t ≤ Real.sqrt (2 / E) → 0 ≤ f t) (z : ℝ) (hz0 : 0 ≤ z) (hzx : z ≤ Real.sqrt (2 / E)) :
    0 ≤ ∫ s in (0 : ℝ)..z, (s ^ 2 - E + E) * f s *
      Real.sin (Real.sqrt E * (z - s)) := by
  refine intervalIntegral.integral_nonneg hz0 (fun s hs => ?_)
  have hs0 : 0 ≤ s := hs.1
  have hsz : s ≤ z := hs.2
  have hfs : 0 ≤ f s := hnn s hs0 (le_trans hsz hzx)
  have hsin : 0 ≤ Real.sin (Real.sqrt E * (z - s)) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (Real.sqrt_nonneg E) ?_) ?_
    · exact sub_nonneg.2 hsz
    · exact le_trans (comparison_sqrtE_mul_short_le_sqrt2 hE
        (le_trans (sub_le_self z hs0) hzx)) comparison_sqrt2_lt_pi.le
  have hprod : (s ^ 2 - E + E) * f s * Real.sin (Real.sqrt E * (z - s)) =
      s ^ 2 * f s * Real.sin (Real.sqrt E * (z - s)) := by ring
  rw [hprod]
  exact mul_nonneg (mul_nonneg (sq_nonneg s) hfs) hsin

/-- The upper-kernel integral `∫₀^x (s² - 2/E) f(s) sin(√q₀ (x-s)) ds` is
nonpositive whenever `f ≥ 0` on `[0, x]` and `x ≤ √(2/E)`. -/
theorem comparison_upper_integral_nonpos (hE : 7 ≤ E) (hnn : ∀ t, 0 ≤ t →
    t ≤ Real.sqrt (2 / E) → 0 ≤ f t) (x : ℝ) (hx0 : 0 ≤ x) (hxx : x ≤ Real.sqrt (2 / E)) :
    ∫ s in (0 : ℝ)..x, (s ^ 2 - 2 / E) * f s *
      Real.sin (Real.sqrt (E - 2 / E) * (x - s)) ≤ 0 := by
  have hEpos : 0 < E := by linarith
  have hx0sq : Real.sqrt (2 / E) ^ 2 = 2 / E := Real.sq_sqrt (le_of_lt (div_pos two_pos hEpos))
  have hneg : 0 ≤ ∫ s in (0 : ℝ)..x, -((s ^ 2 - 2 / E) * f s *
      Real.sin (Real.sqrt (E - 2 / E) * (x - s))) := by
    refine intervalIntegral.integral_nonneg hx0 (fun s hs => ?_)
    have hs0 : 0 ≤ s := hs.1
    have hsx : s ≤ x := hs.2
    have hfs : 0 ≤ f s := hnn s hs0 (le_trans hsx hxx)
    have hsqle : s ^ 2 ≤ 2 / E := by
      have hxx0 : 0 ≤ Real.sqrt (2 / E) := Real.sqrt_nonneg _
      have h1 : s ^ 2 ≤ Real.sqrt (2 / E) ^ 2 :=
        sq_le_sq' (by linarith) (le_trans hsx hxx)
      rw [hx0sq] at h1
      exact h1
    have hsin : 0 ≤ Real.sin (Real.sqrt (E - 2 / E) * (x - s)) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (Real.sqrt_nonneg _) ?_) ?_
      · exact sub_nonneg.2 hsx
      · exact le_trans (comparison_sqrtq0_mul_short_le_sqrt2 hE
          (le_trans (sub_le_self x hs0) hxx) (sub_nonneg.2 hsx)) comparison_sqrt2_lt_pi.le
    have hprod : -((s ^ 2 - 2 / E) * f s * Real.sin (Real.sqrt (E - 2 / E) * (x - s))) =
        ((2 / E - s ^ 2) * f s) * Real.sin (Real.sqrt (E - 2 / E) * (x - s)) := by ring
    rw [hprod]
    exact mul_nonneg (mul_nonneg (by linarith) hfs) hsin
  have hsplit : ∫ s in (0 : ℝ)..x, -((s ^ 2 - 2 / E) * f s *
      Real.sin (Real.sqrt (E - 2 / E) * (x - s))) =
      -∫ s in (0 : ℝ)..x, (s ^ 2 - 2 / E) * f s *
        Real.sin (Real.sqrt (E - 2 / E) * (x - s)) :=
    intervalIntegral.integral_neg
  linarith

/-! ## Section 3: the two-sided sine comparison on `[0, √(2/E)]` -/

/-- **Lower sine comparison** (first half of PROOF.md (3)):
`A/√E · sin(√E x) ≤ f x` on `[0, √(2/E)]`. -/
theorem sine_lower (hE : 7 ≤ E) (hA : 0 < A) (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t) (hf0 : f 0 = 0) (hg0 : g 0 = A)
    (x : ℝ) (hx : 0 ≤ x) (hx0 : x ≤ Real.sqrt (2 / E)) :
    A / Real.sqrt E * Real.sin (Real.sqrt E * x) ≤ f x := by
  have hEpos : 0 < E := by linarith
  have hsqrtE : 0 < Real.sqrt E := Real.sqrt_pos.2 hEpos
  have hnn : ∀ t, 0 ≤ t → t ≤ Real.sqrt (2 / E) → 0 ≤ f t :=
    odesys_nonneg hE hA hf hg hf0 hg0
  have hd : Real.sqrt E * f x = A * Real.sin (Real.sqrt E * x) +
      ∫ s in (0 : ℝ)..x, (s ^ 2 - E + E) * f s * Real.sin (Real.sqrt E * (x - s)) :=
    duhamel_identity hf hg hf0 hg0 E (le_of_lt hEpos) x
  have hint := comparison_lower_integral_nonneg hE hnn x hx hx0
  have h1 : A * Real.sin (Real.sqrt E * x) ≤ Real.sqrt E * f x := by linarith
  have h2 : (A * Real.sin (Real.sqrt E * x)) / Real.sqrt E ≤ f x :=
    (div_le_iff₀ hsqrtE).2 (by linarith [h1, mul_comm (f x) (Real.sqrt E)])
  have h3 : A / Real.sqrt E * Real.sin (Real.sqrt E * x) =
      (A * Real.sin (Real.sqrt E * x)) / Real.sqrt E := by ring
  rw [h3]; exact h2

/-- **Upper sine comparison** (second half of PROOF.md (3)):
`f x ≤ A/√q₀ · sin(√q₀ x)` on `[0, √(2/E)]`, where `q₀ = E - 2/E`. -/
theorem sine_upper (hE : 7 ≤ E) (hA : 0 < A) (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t) (hf0 : f 0 = 0) (hg0 : g 0 = A)
    (x : ℝ) (hx : 0 ≤ x) (hx0 : x ≤ Real.sqrt (2 / E)) :
    f x ≤ A / Real.sqrt (E - 2 / E) * Real.sin (Real.sqrt (E - 2 / E) * x) := by
  have hq0pos : 0 < E - 2 / E := comparison_q0_pos hE
  have hsqrtq0 : 0 < Real.sqrt (E - 2 / E) := Real.sqrt_pos.2 hq0pos
  have hnn : ∀ t, 0 ≤ t → t ≤ Real.sqrt (2 / E) → 0 ≤ f t :=
    odesys_nonneg hE hA hf hg hf0 hg0
  have hd : Real.sqrt (E - 2 / E) * f x = A * Real.sin (Real.sqrt (E - 2 / E) * x) +
      ∫ s in (0 : ℝ)..x, (s ^ 2 - E + (E - 2 / E)) * f s *
        Real.sin (Real.sqrt (E - 2 / E) * (x - s)) :=
    duhamel_identity hf hg hf0 hg0 (E - 2 / E) (le_of_lt hq0pos) x
  -- the kernel (s^2 - E + (E - 2/E)) agrees with (s^2 - 2/E), so the integral is ≤ 0
  have hint : ∫ s in (0 : ℝ)..x, (s ^ 2 - E + (E - 2 / E)) * f s *
      Real.sin (Real.sqrt (E - 2 / E) * (x - s)) ≤ 0 := by
    have h0 := comparison_upper_integral_nonpos hE hnn x hx hx0
    have hcongr := intervalIntegral.integral_congr (a := 0) (b := x) (μ := volume)
      (f := fun s => (s ^ 2 - E + (E - 2 / E)) * f s *
        Real.sin (Real.sqrt (E - 2 / E) * (x - s)))
      (g := fun s => (s ^ 2 - 2 / E) * f s *
        Real.sin (Real.sqrt (E - 2 / E) * (x - s)))
      (fun s _ => by ring)
    linarith
  have h1 : Real.sqrt (E - 2 / E) * f x ≤ A * Real.sin (Real.sqrt (E - 2 / E) * x) := by
    linarith
  have h2 : f x ≤ (A * Real.sin (Real.sqrt (E - 2 / E) * x)) / Real.sqrt (E - 2 / E) :=
    (le_div_iff₀ hsqrtq0).2 (by linarith [h1, mul_comm (f x) (Real.sqrt (E - 2 / E))])
  have h3 : (A * Real.sin (Real.sqrt (E - 2 / E) * x)) / Real.sqrt (E - 2 / E) =
      A / Real.sqrt (E - 2 / E) * Real.sin (Real.sqrt (E - 2 / E) * x) := by ring
  exact h2.trans h3.le

/-- **The complete Section 3 comparison** (PROOF.md (3)): for the generic ODE
system with `E ≥ 7`, `A > 0`, `f 0 = 0`, `g 0 = A`, no positivity of `f` is
assumed; both bounds are proved outright. -/
theorem sine_comparison (hE : 7 ≤ E) (hA : 0 < A) (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t) (hf0 : f 0 = 0) (hg0 : g 0 = A) :
    ∀ x, 0 ≤ x → x ≤ Real.sqrt (2 / E) →
      A / Real.sqrt E * Real.sin (Real.sqrt E * x) ≤ f x ∧
        f x ≤ A / Real.sqrt (E - 2 / E) * Real.sin (Real.sqrt (E - 2 / E) * x) := by
  intro x hx hx0
  exact ⟨sine_lower hE hA hf hg hf0 hg0 x hx hx0, sine_upper hE hA hf hg hf0 hg0 x hx hx0⟩

/-! ## Section 5: strict energy loss at `x0 = √(2/E)` -/

/-- The generic energy `B(x) = (E - x²) f(x)² + g(x)²` for the ODE system. -/
def genEnergy (E : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ := (E - x ^ 2) * f x ^ 2 + g x ^ 2

/-- Pointwise derivative of the generic energy: `B'(x) = -2 x f(x)²`,
using the ODE system (the `f g` and `g f` cross terms cancel exactly). -/
theorem comparison_genEnergy_deriv_raw (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t) (t : ℝ) :
    HasDerivAt (genEnergy E f g)
      (((-2 * t) * f t ^ 2 + (E - t ^ 2) * (2 * f t * g t)) +
        2 * g t * ((t ^ 2 - E) * f t)) t := by
  have hq : HasDerivAt (fun t => E - t ^ 2) (-2 * t) t := by
    simpa using ((hasDerivAt_id t).pow 2).const_sub E
  have hf2 : HasDerivAt (fun t => f t ^ 2) (2 * f t * g t) t := by
    refine (((hf t).pow 2).congr_deriv (by ring)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun u => by simp)
  have hg2 : HasDerivAt (fun t => g t ^ 2) (2 * g t * ((t ^ 2 - E) * f t)) t := by
    refine (((hg t).pow 2).congr_deriv (by ring)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun u => by simp)
  refine (((hq.mul hf2).add hg2).congr_of_eventuallyEq ?_)
  exact Filter.Eventually.of_forall (fun u => by simp [genEnergy])

/-- The strict energy-loss integral bound:
`∫₀^{x0} 2 s f(s)² ds ≥ 25 A² / (36 E²)`, proved from the lower sine
comparison and the substitution `u = √E s`. -/
theorem comparison_loss_integral_lower (hE : 7 ≤ E) (hA : 0 < A)
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t)
    (hf0 : f 0 = 0) (hg0 : g 0 = A) :
    (25 : ℝ) * A ^ 2 / (36 * E ^ 2) ≤ ∫ s in (0 : ℝ)..Real.sqrt (2 / E), 2 * s * f s ^ 2 := by
  have hEpos : 0 < E := by linarith
  have hfc : Continuous f := odesys_continuous_f hf
  have hgc : Continuous g := odesys_continuous_g hg
  set x0 := Real.sqrt (2 / E) with hx0def
  have hx0pos : 0 < x0 := Real.sqrt_pos.2 (div_pos two_pos hEpos)
  have hsqrtE : 0 < Real.sqrt E := Real.sqrt_pos.2 hEpos
  have hnn : ∀ t, 0 ≤ t → t ≤ x0 → 0 ≤ f t := odesys_nonneg hE hA hf hg hf0 hg0
  -- Step 1: pointwise lower bound via the lower sine comparison
  have hstep1 : (∫ s in (0 : ℝ)..x0, 2 * s * f s ^ 2) ≥
      ∫ s in (0 : ℝ)..x0, (2 * A ^ 2 / E) * s * Real.sin (Real.sqrt E * s) ^ 2 := by
    have hcont1 : Continuous (fun s : ℝ => 2 * s * f s ^ 2) := by fun_prop
    have hcont2 : Continuous (fun s : ℝ => (2 * A ^ 2 / E) * s *
      Real.sin (Real.sqrt E * s) ^ 2) := by fun_prop
    refine intervalIntegral.integral_mono_on hx0pos.le
      (hcont2.intervalIntegrable 0 x0) (hcont1.intervalIntegrable 0 x0) ?_
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hfs : 0 ≤ f s := hnn s hs0 hs.2
    have hsinpos : 0 ≤ A / Real.sqrt E * Real.sin (Real.sqrt E * s) := by
      refine mul_nonneg (div_nonneg hA.le (Real.sqrt_nonneg E)) ?_
      refine Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (Real.sqrt_nonneg E) hs0) ?_
      exact le_trans (comparison_sqrtE_mul_short_le_sqrt2 hE hs.2) comparison_sqrt2_lt_pi.le
    have hfs2 : (A / Real.sqrt E * Real.sin (Real.sqrt E * s)) ^ 2 ≤ f s ^ 2 := by
      refine sq_le_sq' (h1 := ?_) (h2 := ?_)
      · linarith
      · exact sine_lower hE hA hf hg hf0 hg0 s hs0 hs.2
    have hcoef : (A / Real.sqrt E * Real.sin (Real.sqrt E * s)) ^ 2 =
        (A ^ 2 / E) * Real.sin (Real.sqrt E * s) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (le_of_lt hEpos)]
    have h2s : 0 ≤ 2 * s := by linarith
    have key := mul_le_mul_of_nonneg_left hfs2 h2s
    have hcoef2 : (2 * s) * ((A / Real.sqrt E * Real.sin (Real.sqrt E * s)) ^ 2)
        = (2 * A ^ 2 / E) * s * Real.sin (Real.sqrt E * s) ^ 2 := by
      rw [hcoef]; ring
    rw [hcoef2] at key
    exact key
  -- Step 2: substitute u = √E s
  have hstep2 : ∫ s in (0 : ℝ)..x0, (2 * A ^ 2 / E) * s * Real.sin (Real.sqrt E * s) ^ 2
      = (2 * A ^ 2 / E ^ 2) * ∫ u in (0 : ℝ)..Real.sqrt 2, u * Real.sin u ^ 2 := by
    have hcst : ∀ s : ℝ, (2 * A ^ 2 / E) * s * Real.sin (Real.sqrt E * s) ^ 2 =
        (2 * A ^ 2 / (E * Real.sqrt E)) *
          ((fun u : ℝ => u * Real.sin u ^ 2) (Real.sqrt E * s)) := by
      intro s
      have hE0 : Real.sqrt E ≠ 0 := ne_of_gt hsqrtE
      show (2 * A ^ 2 / E) * s * Real.sin (Real.sqrt E * s) ^ 2 =
        (2 * A ^ 2 / (E * Real.sqrt E)) *
          (Real.sqrt E * s * Real.sin (Real.sqrt E * s) ^ 2)
      field_simp
    have hcongr := intervalIntegral.integral_congr (a := 0) (b := x0) (μ := volume)
      (f := fun s => (2 * A ^ 2 / E) * s * Real.sin (Real.sqrt E * s) ^ 2)
      (g := fun s => (2 * A ^ 2 / (E * Real.sqrt E)) *
        ((fun u : ℝ => u * Real.sin u ^ 2) (Real.sqrt E * s)))
      (fun s _ => by
        have hE0 : Real.sqrt E ≠ 0 := ne_of_gt hsqrtE
        show (2 * A ^ 2 / E) * s * Real.sin (Real.sqrt E * s) ^ 2 =
          (2 * A ^ 2 / (E * Real.sqrt E)) *
            (Real.sqrt E * s * Real.sin (Real.sqrt E * s) ^ 2)
        field_simp)
    have hcomp := intervalIntegral.integral_comp_mul_left
      (f := fun u : ℝ => u * Real.sin u ^ 2) (a := (0 : ℝ)) (b := x0) (c := Real.sqrt E)
      (ne_of_gt hsqrtE)
    have hlim : Real.sqrt E * x0 = Real.sqrt 2 := by
      have hmul : E * (2 / E) = 2 := by field_simp
      rw [hx0def, ← Real.sqrt_mul hEpos.le, hmul]
    calc ∫ s in (0 : ℝ)..x0, (2 * A ^ 2 / E) * s * Real.sin (Real.sqrt E * s) ^ 2
        = ∫ s in (0 : ℝ)..x0, (2 * A ^ 2 / (E * Real.sqrt E)) *
            ((fun u : ℝ => u * Real.sin u ^ 2) (Real.sqrt E * s)) := hcongr
      _ = (2 * A ^ 2 / (E * Real.sqrt E)) * ∫ s in (0 : ℝ)..x0,
            (fun u : ℝ => u * Real.sin u ^ 2) (Real.sqrt E * s) := by
            rw [intervalIntegral.integral_const_mul]
      _ = (2 * A ^ 2 / (E * Real.sqrt E)) * ((Real.sqrt E)⁻¹ *
            ∫ u in Real.sqrt E * 0..Real.sqrt E * x0, u * Real.sin u ^ 2) := by
            rw [hcomp, smul_eq_mul]
      _ = (2 * A ^ 2 / E ^ 2) * ∫ u in (0 : ℝ)..Real.sqrt 2, u * Real.sin u ^ 2 := by
            rw [hlim, mul_zero]
            have hE0 : Real.sqrt E ≠ 0 := ne_of_gt hsqrtE
            field_simp
            rw [Real.sq_sqrt (le_of_lt hEpos)]
  -- Step 3: bound ∫₀^{√2} u sin²u du ≥ 25/72
  have hM : (25 : ℝ) / 72 ≤ ∫ u in (0 : ℝ)..Real.sqrt 2, u * Real.sin u ^ 2 := by
    have hcont : Continuous (fun u : ℝ => u * Real.sin u ^ 2) := by fun_prop
    have hsplit : (∫ u in (0 : ℝ)..1, (u * Real.sin u ^ 2)) +
        (∫ u in 1..Real.sqrt 2, (u * Real.sin u ^ 2)) =
        (∫ u in (0 : ℝ)..Real.sqrt 2, (u * Real.sin u ^ 2)) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (μ := volume) 0 1)
        (hcont.intervalIntegrable (μ := volume) 1 (Real.sqrt 2))
    have h01 : 0 ≤ ∫ u in (0 : ℝ)..1, u * Real.sin u ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1) (fun u hu => by
        refine mul_nonneg hu.1 (sq_nonneg _))
    have hpt : ∀ u ∈ Icc 1 (Real.sqrt 2), (25 : ℝ) / 36 * u ≤ u * Real.sin u ^ 2 := by
      intro u hu
      have hsin : (5 : ℝ) / 6 ≤ Real.sin u := by
        have h1le : (1 : ℝ) ≤ Real.pi / 2 := le_trans (by norm_num) comparison_sqrt2_le_pi_div_two
        have h2 : Real.sin 1 ≤ Real.sin u := by
          refine Real.monotoneOn_sin (mem_Icc.2 ⟨by linarith [Real.pi_pos], h1le⟩)
            (mem_Icc.2 ⟨by linarith [hu.1, Real.pi_pos], le_trans hu.2 comparison_sqrt2_le_pi_div_two⟩)
            hu.1
        linarith [comparison_sin_one_ge_five_six]
      have hsq : (25 : ℝ) / 36 ≤ Real.sin u ^ 2 := by
        have hk := sq_le_sq' (a := (5 : ℝ) / 6) (b := Real.sin u)
          (by linarith [Real.sin_nonneg_of_nonneg_of_le_pi (le_refl (0:ℝ)) Real.pi_pos.le])
          hsin
        norm_num at hk
        exact hk
      calc (25 : ℝ) / 36 * u = u * ((25 : ℝ) / 36) := by ring
        _ ≤ u * Real.sin u ^ 2 := mul_le_mul_of_nonneg_left hsq (by linarith [hu.1])
    have hcont3 : Continuous (fun u : ℝ => (25 : ℝ) / 36 * u) := by fun_prop
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ Real.sqrt 2)
      (hcont3.intervalIntegrable (μ := volume) 1 (Real.sqrt 2))
      (hcont.intervalIntegrable (μ := volume) 1 (Real.sqrt 2)) hpt
    have hI2 : ∫ u in (1 : ℝ)..Real.sqrt 2, (25 : ℝ) / 36 * u = (25 : ℝ) / 72 := by
      rw [intervalIntegral.integral_const_mul]
      norm_num [integral_pow,
        show Real.sqrt 2 ^ 2 = (2 : ℝ) from Real.sq_sqrt (by norm_num)]
    linarith
  -- combine
  calc (25 : ℝ) * A ^ 2 / (36 * E ^ 2)
      = (2 * A ^ 2 / E ^ 2) * ((25 : ℝ) / 72) := by field_simp; ring
    _ ≤ (2 * A ^ 2 / E ^ 2) * ∫ u in (0 : ℝ)..Real.sqrt 2, u * Real.sin u ^ 2 := by
        exact mul_le_mul_of_nonneg_left hM (by positivity)
    _ ≤ ∫ s in (0 : ℝ)..x0, 2 * s * f s ^ 2 := by
        rw [← hstep2]; exact hstep1

/-- **Strict energy loss** (PROOF.md (5), first display):
`B(x0) < A² (1 - 1/(2E²))` at `x0 = √(2/E)`, via the exact energy derivative
`B' = -2x f²`, the fundamental theorem of calculus, and the lower sine
comparison. -/
theorem energy_loss (hE : 7 ≤ E) (hA : 0 < A) (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t) (hf0 : f 0 = 0) (hg0 : g 0 = A) :
    genEnergy E f g (Real.sqrt (2 / E)) < A ^ 2 * (1 - 1 / (2 * E ^ 2)) := by
  have hEpos : 0 < E := by linarith
  have hfc : Continuous f := odesys_continuous_f hf
  have hgc : Continuous g := odesys_continuous_g hg
  set x0 := Real.sqrt (2 / E) with hx0def
  have hx0pos : 0 < x0 := Real.sqrt_pos.2 (div_pos two_pos hEpos)
  -- exact energy derivative and FTC
  have hint : IntervalIntegrable
      (fun s => ((-2 * s) * f s ^ 2 + (E - s ^ 2) * (2 * f s * g s)) +
        2 * g s * ((s ^ 2 - E) * f s)) volume 0 x0 := by
    exact (by fun_prop : Continuous
      (fun s => ((-2 * s) * f s ^ 2 + (E - s ^ 2) * (2 * f s * g s)) +
        2 * g s * ((s ^ 2 - E) * f s))).intervalIntegrable 0 x0
  have hFTC : ∫ s in (0 : ℝ)..x0,
      (((-2 * s) * f s ^ 2 + (E - s ^ 2) * (2 * f s * g s)) +
        2 * g s * ((s ^ 2 - E) * f s)) =
      genEnergy E f g x0 - genEnergy E f g 0 :=
    integral_eq_sub_of_hasDerivAt (fun s _ => comparison_genEnergy_deriv_raw hf hg s) hint
  have hB0 : genEnergy E f g 0 = A ^ 2 := by simp [genEnergy, hf0, hg0]
  -- rewrite the raw derivative integrand as -2 s f(s)²
  have hcongr := intervalIntegral.integral_congr (a := 0) (b := x0) (μ := volume)
    (f := fun s => ((-2 * s) * f s ^ 2 + (E - s ^ 2) * (2 * f s * g s)) +
      2 * g s * ((s ^ 2 - E) * f s))
    (g := fun s => -2 * s * f s ^ 2) (fun s _ => by ring)
  have hnegI : ∫ s in (0 : ℝ)..x0, -2 * s * f s ^ 2 =
      -(∫ s in (0 : ℝ)..x0, 2 * s * f s ^ 2) := by
    have h1 := intervalIntegral.integral_congr (a := 0) (b := x0) (μ := volume)
      (f := fun s => -2 * s * f s ^ 2) (g := fun s => -(2 * s * f s ^ 2))
      (fun s _ => by ring)
    rw [h1, intervalIntegral.integral_neg]
  have hgen : genEnergy E f g x0 = A ^ 2 - ∫ s in (0 : ℝ)..x0, 2 * s * f s ^ 2 := by
    have h := hFTC
    rw [hcongr] at h
    rw [hnegI] at h
    linarith [h, hB0]
  -- the loss bound
  have hloss := comparison_loss_integral_lower hE hA hf hg hf0 hg0
  -- ratio: 25 A²/(36 E²) > A²/(2 E²)
  have hratio : (25 : ℝ) * A ^ 2 / (36 * E ^ 2) > A ^ 2 / (2 * E ^ 2) := by
    have hP : 0 < A ^ 2 / E ^ 2 :=
      div_pos (sq_pos_of_ne_zero (ne_of_gt hA)) (sq_pos_of_ne_zero (ne_of_gt hEpos))
    have h1 : (25 : ℝ) * A ^ 2 / (36 * E ^ 2)
        = 1 / 2 * (A ^ 2 / E ^ 2) + 7 / 36 * (A ^ 2 / E ^ 2) := by ring
    have h2 : A ^ 2 / (2 * E ^ 2) = 1 / 2 * (A ^ 2 / E ^ 2) := by ring
    rw [h1, h2]
    have : 0 < 7 / 36 * (A ^ 2 / E ^ 2) := mul_pos (by norm_num) hP
    linarith
  calc genEnergy E f g x0 = A ^ 2 - ∫ s in (0 : ℝ)..x0, 2 * s * f s ^ 2 := hgen
    _ ≤ A ^ 2 - (25 : ℝ) * A ^ 2 / (36 * E ^ 2) := by linarith
    _ < A ^ 2 - A ^ 2 / (2 * E ^ 2) := by linarith
    _ = A ^ 2 * (1 - 1 / (2 * E ^ 2)) := by ring

end HermiteEnvelope
