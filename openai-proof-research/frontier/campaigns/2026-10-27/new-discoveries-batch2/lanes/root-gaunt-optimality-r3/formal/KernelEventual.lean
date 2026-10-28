import LaplaceSign
import ComparisonKernel

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace GauntIntegral

def comparisonBessel (v m r x : ℝ) : ℝ :=
  besselK m x - besselK (r - 1) x - (v + r) / x * besselK r x

theorem comparisonKernel_integral (v m : ℝ) {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-x * Real.cosh u) * comparisonKernel v m r u) =
      comparisonBessel v m r x := by
  have hm := (besselIntegrand_integrable m hx).integrableOn (s := Ioi (0 : ℝ))
  have hp := (besselIntegrand_integrable (r + 1) hx).integrableOn (s := Ioi (0 : ℝ))
  have hn := (besselIntegrand_integrable (r - 1) hx).integrableOn (s := Ioi (0 : ℝ))
  have heq : (fun u => Real.exp (-x * Real.cosh u) * comparisonKernel v m r u) =
      (fun u => besselIntegrand m x u - (v + r) / (2 * r) * besselIntegrand (r + 1) x u -
        (r - v) / (2 * r) * besselIntegrand (r - 1) x u) := by
    ext u
    dsimp [besselIntegrand, comparisonKernel]
    ring
  have hsub := integral_sub (hm.sub (hp.const_mul ((v + r) / (2 * r))))
    (hn.const_mul ((r - v) / (2 * r)))
  simp only [Pi.sub_apply] at hsub
  rw [heq, hsub,
    integral_sub hm (hp.const_mul ((v + r) / (2 * r))), integral_const_mul, integral_const_mul]
  change besselK m x - (v + r) / (2 * r) * besselK (r + 1) x -
    (r - v) / (2 * r) * besselK (r - 1) x = comparisonBessel v m r x
  have hrec := eq_add_of_sub_eq (besselK_recurrence hx r)
  rw [hrec]
  unfold comparisonBessel
  field_simp
  ring

theorem comparisonBessel_eventually_negative {d v m r : ℝ} (hd : 0 ≤ d) (hdr : d < r)
    (hm : m ^ 2 = d ^ 2 + 2 * v + 1) :
    ∀ᶠ x : ℝ in atTop, comparisonBessel v m r x < 0 := by
  obtain ⟨e, he, hneg⟩ := comparisonKernel_negative_near_zero hd hdr hm
  let a : ℝ := e / 3
  let b : ℝ := 2 * e / 3
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hbe : b < e := by dsimp [b]; linarith
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc a b).Nonempty from ⟨a, le_rfl, hab.le⟩)
    (show ContinuousOn (comparisonKernel v m r) (Icc a b) by unfold comparisonKernel; fun_prop)
  have hz0 : 0 < z := ha.trans_le hz.1
  have hze : z ≤ e := hz.2.trans hbe.le
  have hzneg := hneg z ⟨hz0, hze⟩
  have hnear : ∀ u ∈ Ioc (0 : ℝ) e, comparisonKernel v m r u ≤ 0 :=
    fun u hu => (hneg u hu).le
  have hwindow : ∀ u ∈ Icc a b, comparisonKernel v m r u ≤ -(-comparisonKernel v m r z) := by
    intro u hu
    simpa only [neg_neg, mem_ofPred_eq] using hmax hu
  have hevent := laplace_eventually_negative ha hab hbe (neg_pos.mpr hzneg) hnear hwindow
    (fun x hx => comparisonKernel_integrable v m r hx)
  filter_upwards [hevent, eventually_gt_atTop (0 : ℝ)] with x h hx
  rwa [comparisonKernel_integral v m (hd.trans_lt hdr) hx] at h

end GauntIntegral
