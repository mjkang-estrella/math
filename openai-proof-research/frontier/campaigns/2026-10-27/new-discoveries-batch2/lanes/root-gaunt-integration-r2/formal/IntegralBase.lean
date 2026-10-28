import SquaredOrder

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
noncomputable section

namespace GauntIntegral

def besselIntegrand (v x u : ℝ) : ℝ :=
  Real.exp (-x * Real.cosh u) * Real.cosh (v * u)

def besselK (v x : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), besselIntegrand v x u

theorem cosh_le_exp_abs (u : ℝ) : Real.cosh u ≤ Real.exp |u| := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_le_exp.mpr (le_abs_self u)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs u)
  linarith

theorem half_sq_le_cosh (u : ℝ) : u ^ 2 / 2 ≤ Real.cosh u := by
  have h := (Real.hasSum_cosh u).summable.le_tsum 1 (fun k _ => by
    apply div_nonneg
    · rw [pow_mul]
      exact pow_nonneg (sq_nonneg u) k
    · positivity)
  simpa using h.trans_eq (Real.hasSum_cosh u).tsum_eq

theorem linear_le_quadratic (q : ℝ) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    q * |u| ≤ x / 4 * u ^ 2 + q ^ 2 / x := by
  have hh := sq_nonneg (x * |u| - 2 * q)
  rw [sub_sq, mul_pow, sq_abs] at hh
  have hdiv : x * (q ^ 2 / x) = q ^ 2 := by field_simp
  apply (mul_le_mul_iff_left₀ hx).mp
  nlinarith

theorem besselIntegrand_gaussian_bound (v : ℝ) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    besselIntegrand v x u ≤
      Real.exp (|v| ^ 2 / x) * Real.exp (-(x / 4) * u ^ 2) := by
  have hc := half_sq_le_cosh u
  have hl := linear_le_quadratic |v| hx u
  calc
    besselIntegrand v x u ≤ Real.exp (-x * Real.cosh u) * Real.exp |v * u| := by
      exact mul_le_mul_of_nonneg_left (cosh_le_exp_abs (v * u)) (by positivity)
    _ = Real.exp (-x * Real.cosh u + |v| * |u|) := by rw [abs_mul, Real.exp_add]
    _ ≤ Real.exp (|v| ^ 2 / x - x / 4 * u ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (|v| ^ 2 / x) * Real.exp (-(x / 4) * u ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem besselIntegrand_integrable (v : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable (besselIntegrand v x) := by
  have hg := (integrable_exp_neg_mul_sq (b := x / 4) (by linarith)).const_mul
    (Real.exp (|v| ^ 2 / x))
  refine hg.mono' (by unfold besselIntegrand; fun_prop) ?_
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact besselIntegrand_gaussian_bound v hx u
  · unfold besselIntegrand
    positivity

theorem besselK_squaredOrder_strictConvex {x : ℝ} (hx : 0 < x) :
    StrictConvexOn ℝ (Ici 0) (fun a : ℝ => besselK (Real.sqrt a) x) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro a ha b hb hab s t hs ht hst
  have hpoint : ∀ u : ℝ, 0 < u →
      besselIntegrand (Real.sqrt (s * a + t * b)) x u <
        s * besselIntegrand (Real.sqrt a) x u +
          t * besselIntegrand (Real.sqrt b) x u := by
    intro u hu
    have h := (orderKernel_strictConvex (ne_of_gt hu)).2 ha hb hab hs ht hst
    have h' := mul_lt_mul_of_pos_left h (Real.exp_pos (-x * Real.cosh u))
    simpa only [besselIntegrand, orderKernel, smul_eq_mul, mul_add,
      mul_assoc, mul_left_comm, mul_comm] using h'
  let f : ℝ → ℝ := fun u => s * besselIntegrand (Real.sqrt a) x u +
    t * besselIntegrand (Real.sqrt b) x u -
      besselIntegrand (Real.sqrt (s * a + t * b)) x u
  have hf1 := (besselIntegrand_integrable (Real.sqrt a) hx).integrableOn
    (s := Ioi (0 : ℝ))
  have hf2 := (besselIntegrand_integrable (Real.sqrt b) hx).integrableOn
    (s := Ioi (0 : ℝ))
  have hf3 := (besselIntegrand_integrable (Real.sqrt (s * a + t * b)) hx).integrableOn
    (s := Ioi (0 : ℝ))
  have hf : IntegrableOn f (Ioi (0 : ℝ)) :=
    ((hf1.const_mul s).add (hf2.const_mul t)).sub hf3
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    dsimp [f]
    linarith [hpoint u hu]
  have hsub : Ioo (1 : ℝ) 2 ⊆ Function.support f ∩ Ioi 0 := by
    intro u hu
    have hu0 : 0 < u := lt_trans (by norm_num : (0 : ℝ) < 1) hu.1
    refine ⟨?_, hu0⟩
    change f u ≠ 0
    dsimp [f]
    linarith [hpoint u hu0]
  have hp : 0 < ∫ u in Ioi (0 : ℝ), f u :=
    (setIntegral_pos_iff_support_of_nonneg_ae hn hf).2
      (lt_of_lt_of_le (by norm_num) (measure_mono hsub))
  dsimp [f] at hp
  have hdiff := integral_sub ((hf1.const_mul s).add (hf2.const_mul t)) hf3
  simp only [Pi.add_apply] at hdiff
  rw [hdiff] at hp
  have hadd := integral_add (hf1.const_mul s) (hf2.const_mul t)
  rw [hadd, integral_const_mul, integral_const_mul] at hp
  change 0 < s * besselK (Real.sqrt a) x + t * besselK (Real.sqrt b) x -
    besselK (Real.sqrt (s * a + t * b)) x at hp
  simpa only [smul_eq_mul] using (sub_pos.mp hp)

theorem besselK_neg (v x : ℝ) : besselK (-v) x = besselK v x := by
  simp only [besselK, besselIntegrand, neg_mul, Real.cosh_neg]

theorem besselK_abs (v x : ℝ) : besselK |v| x = besselK v x := by
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
  · rw [abs_of_nonpos hv, besselK_neg]

theorem besselK_sqrt_sq (v x : ℝ) :
    besselK (Real.sqrt (v ^ 2)) x = besselK v x := by
  rw [Real.sqrt_sq_eq_abs, besselK_abs]

theorem besselK_three_order {x d v m : ℝ} (hx : 0 < x)
    (hd : 0 < d) (hdv : d < v) (hm : m ^ 2 = d ^ 2 + 2 * v + 1) :
    (v + d) * besselK (d + 1) x + (d - v) * besselK (d - 1) x <
      (2 * d) * besselK m x := by
  have hv : 0 < v := lt_trans hd hdv
  have hc : 0 ≤ d ^ 2 + 2 * v + 1 := by positivity
  have hab : (d - 1) ^ 2 < (d + 1) ^ 2 := by nlinarith
  have hbc : (d + 1) ^ 2 < d ^ 2 + 2 * v + 1 := by nlinarith
  have h := (besselK_squaredOrder_strictConvex hx).secant_strict_mono_aux1
    (show (d - 1) ^ 2 ∈ Ici (0 : ℝ) by simpa only [mem_Ici] using sq_nonneg (d - 1))
    (show d ^ 2 + 2 * v + 1 ∈ Ici (0 : ℝ) by simpa only [mem_Ici] using hc) hab hbc
  rw [← hm, besselK_sqrt_sq, besselK_sqrt_sq, besselK_sqrt_sq] at h
  rw [hm] at h
  nlinarith

end GauntIntegral
