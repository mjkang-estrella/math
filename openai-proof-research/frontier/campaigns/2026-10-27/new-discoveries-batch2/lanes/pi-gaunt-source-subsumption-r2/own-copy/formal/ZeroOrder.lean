import Recurrence

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace GauntIntegral

def zeroTangentIntegrand (x u : ℝ) : ℝ := u * Real.exp (-x * Real.cosh u) * Real.sinh u

theorem zeroTangent_norm_bound {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ‖zeroTangentIntegrand x u‖ ≤
      Real.exp (1 / x) * (|u| * Real.exp (-(x / 4) * u ^ 2)) := by
  have hs := sinh_boundary_norm_bound 1 hx u
  simp only [one_mul, abs_one, one_pow] at hs
  calc
    ‖zeroTangentIntegrand x u‖ = |u| *
        ‖Real.exp (-x * Real.cosh u) * Real.sinh u‖ := by
      rw [zeroTangentIntegrand, mul_assoc, norm_mul, Real.norm_eq_abs]
    _ ≤ |u| * (Real.exp (1 / x) * Real.exp (-(x / 4) * u ^ 2)) :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg u)
    _ = _ := by ring

theorem zeroTangent_integrable {x : ℝ} (hx : 0 < x) :
    Integrable (zeroTangentIntegrand x) := by
  have hg : Integrable (fun u : ℝ => |u| * Real.exp (-(x / 4) * u ^ 2)) := by
    simpa [Real.norm_eq_abs, abs_mul] using
      (integrable_mul_exp_neg_mul_sq (b := x / 4) (by linarith)).norm
  apply (hg.const_mul (Real.exp (1 / x))).mono' (by unfold zeroTangentIntegrand; fun_prop)
  filter_upwards [] with u
  exact zeroTangent_norm_bound hx u

theorem linear_boundary_hasDerivAt (x u : ℝ) :
    HasDerivAt (fun t : ℝ => t * Real.exp (-x * Real.cosh t))
      (besselIntegrand 0 x u - x * zeroTangentIntegrand x u) u := by
  have h := (hasDerivAt_id u).mul (((Real.hasDerivAt_cosh u).const_mul (-x)).exp)
  convert! h using 1
  simp only [besselIntegrand, zeroTangentIntegrand, zero_mul, Real.cosh_zero, mul_one, one_mul, id_eq]
  ring

theorem linear_boundary_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun u : ℝ => u * Real.exp (-x * Real.cosh u)) atTop (𝓝 0) := by
  have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (a := x / 4) (by linarith) (1 : ℝ)
  have h' : Tendsto (fun u : ℝ => |u| * Real.exp (-(x / 4) * u ^ 2)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using h.mono_left atTop_le_cocompact
  apply squeeze_zero_norm (a := fun u : ℝ => |u| * Real.exp (-(x / 4) * u ^ 2)) ?_ h'
  intro u
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg u)
  apply Real.exp_le_exp.mpr
  nlinarith [half_sq_le_cosh u]

theorem zeroTangent_integral {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi (0 : ℝ), zeroTangentIntegrand x u = besselK 0 x / x := by
  have h0 := (besselIntegrand_integrable 0 hx).integrableOn (s := Ioi (0 : ℝ))
  have ht := (zeroTangent_integrable hx).integrableOn (s := Ioi (0 : ℝ))
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u _ => linear_boundary_hasDerivAt x u) (h0.sub (ht.const_mul x))
    (linear_boundary_tendsto hx)
  simp only [zero_mul, sub_zero] at hi
  rw [integral_sub h0 (ht.const_mul x), integral_const_mul] at hi
  change besselK 0 x - x * ∫ u in Ioi (0 : ℝ), zeroTangentIntegrand x u = 0 at hi
  apply (eq_div_iff (ne_of_gt hx)).mpr
  nlinarith

theorem integral_Ioi_strict_mono {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hg : IntegrableOn g (Ioi 0))
    (hfg : ∀ u : ℝ, 0 < u → f u < g u) :
    ∫ u in Ioi (0 : ℝ), f u < ∫ u in Ioi (0 : ℝ), g u := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun u => g u - f u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (sub_pos.mpr (hfg u hu)).le
  have hsub : Ioo (1 : ℝ) 2 ⊆ Function.support (fun u => g u - f u) ∩ Ioi 0 := by
    intro u hu
    have hu0 : 0 < u := lt_trans (by norm_num : (0 : ℝ) < 1) hu.1
    refine ⟨?_, hu0⟩
    change g u - f u ≠ 0
    exact ne_of_gt (sub_pos.mpr (hfg u hu0))
  have hp := (setIntegral_pos_iff_support_of_nonneg_ae hn (hg.sub hf)).2
    (lt_of_lt_of_le (by norm_num) (measure_mono hsub))
  rw [integral_sub hg hf] at hp
  exact sub_pos.mp hp

theorem besselK_zero_order_comparison {x v m : ℝ} (hx : 0 < x)
    (hv : 0 < v) (hm : m ^ 2 = 2 * v + 1) :
    besselK 1 x + v / x * besselK 0 x < besselK m x := by
  have h1 := (besselIntegrand_integrable 1 hx).integrableOn (s := Ioi (0 : ℝ))
  have ht := (zeroTangent_integrable hx).integrableOn (s := Ioi (0 : ℝ))
  have hm' := (besselIntegrand_integrable (Real.sqrt (m ^ 2)) hx).integrableOn
    (s := Ioi (0 : ℝ))
  have hp := integral_Ioi_strict_mono (h1.add (ht.const_mul v)) hm' (fun u hu => by
    have hs := orderKernel_tangent (ne_of_gt hu)
      (show 1 < m ^ 2 by nlinarith)
    have hs' := mul_lt_mul_of_pos_left hs (Real.exp_pos (-x * Real.cosh u))
    dsimp [orderKernel] at hs'
    change besselIntegrand 1 x u + v * zeroTangentIntegrand x u <
      besselIntegrand (Real.sqrt (m ^ 2)) x u
    simp only [besselIntegrand, one_mul, zeroTangentIntegrand]
    rw [hm] at hs'
    rw [hm]
    convert! hs' using 1 <;> ring_nf)
  simp only [Pi.add_apply] at hp
  have hadd := integral_add h1 (ht.const_mul v)
  rw [hadd, integral_const_mul, zeroTangent_integral hx] at hp
  change besselK 1 x + v * (besselK 0 x / x) < besselK (Real.sqrt (m ^ 2)) x at hp
  rw [besselK_sqrt_sq] at hp
  convert hp using 1
  ring

end GauntIntegral
