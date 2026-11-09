import OptimalConverse

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace GauntIntegral

theorem besselK_le_of_abs_le {d r x : ℝ} (hx : 0 < x) (hd : 0 ≤ d) (hr : |r| ≤ d) :
    besselK r x ≤ besselK d x := by
  have hf := (besselIntegrand_integrable r hx).integrableOn (s := Ioi (0 : ℝ))
  have hg := (besselIntegrand_integrable d hx).integrableOn (s := Ioi (0 : ℝ))
  apply integral_mono_ae hf hg
  filter_upwards [] with u
  unfold besselIntegrand
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.cosh_le_cosh.mpr
  have h := mul_le_mul_of_nonneg_right hr (abs_nonneg u)
  simpa only [abs_mul, abs_of_nonneg hd] using h

theorem weightedK_le_of_abs_le {d r x : ℝ} (hx : 0 < x) (hd : 0 ≤ d) (hr : |r| ≤ d)
    (v : ℝ) : weightedK v r x ≤ weightedK v d x := by
  exact mul_le_mul_of_nonneg_left (besselK_le_of_abs_le hx hd hr) (Real.rpow_nonneg hx.le _)

theorem tail_lower_bound_iff_abs_order {d v m r : ℝ} (hd : 0 ≤ d) (hdv : d < v)
    (hm : m ^ 2 = d ^ 2 + 2 * v + 1) :
    (∀ x : ℝ, 0 < x → weightedK v r x < ∫ t in Ioi x, weightedK v m t) ↔ |r| ≤ d := by
  constructor
  · intro hall
    by_contra hfail
    have hdr : d < |r| := not_le.mp hfail
    obtain ⟨x, hx, htail⟩ := (tail_eventually_below_larger_order hd hdv hdr hm).exists
    have h := hall x hx
    simp only [weightedK, besselK_abs] at htail h
    exact (lt_irrefl _ (h.trans htail))
  · intro hr x hx
    exact (weightedK_le_of_abs_le hx hd hr v).trans_lt (tail_strict_lower_bound hx hd hdv hm)

def SourceClaim339406Full : Prop := ∀ n v : ℝ, n < 1 →
  1 - n + Real.sqrt (2 * (1 - n)) ≤ v → ∀ r : ℝ,
    (∀ x : ℝ, 0 < x → x ^ (-v) * besselK r x <
      ∫ t in Ioi x, t ^ (-v) * besselK (v + n) t) ↔ |r| ≤ sourceOrder n v

theorem source_full_classification_339406 : SourceClaim339406Full := by
  intro n v hn hv r
  obtain ⟨hd0, hdv, hm⟩ := source_parameter_geometry hn hv
  exact tail_lower_bound_iff_abs_order hd0 hdv hm

end GauntIntegral
