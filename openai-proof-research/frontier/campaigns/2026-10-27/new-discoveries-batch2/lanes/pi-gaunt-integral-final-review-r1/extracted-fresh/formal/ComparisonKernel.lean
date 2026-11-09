import LocalSign

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace GauntIntegral

def comparisonKernel (v m r u : ℝ) : ℝ := Real.cosh (m * u) -
  (v + r) / (2 * r) * Real.cosh ((r + 1) * u) -
  (r - v) / (2 * r) * Real.cosh ((r - 1) * u)

def comparisonKernelDeriv (v m r u : ℝ) : ℝ := m * Real.sinh (m * u) -
  (v + r) / (2 * r) * (r + 1) * Real.sinh ((r + 1) * u) -
  (r - v) / (2 * r) * (r - 1) * Real.sinh ((r - 1) * u)

def comparisonKernelDeriv2 (v m r u : ℝ) : ℝ := m ^ 2 * Real.cosh (m * u) -
  (v + r) / (2 * r) * (r + 1) ^ 2 * Real.cosh ((r + 1) * u) -
  (r - v) / (2 * r) * (r - 1) ^ 2 * Real.cosh ((r - 1) * u)

theorem comparisonKernel_hasDerivAt (v m r u : ℝ) :
    HasDerivAt (comparisonKernel v m r) (comparisonKernelDeriv v m r u) u := by
  have h := (((Real.hasDerivAt_cosh (m * u)).comp u ((hasDerivAt_id u).const_mul m)).sub
    (((Real.hasDerivAt_cosh ((r + 1) * u)).comp u
      ((hasDerivAt_id u).const_mul (r + 1))).const_mul ((v + r) / (2 * r)))).sub
    (((Real.hasDerivAt_cosh ((r - 1) * u)).comp u
      ((hasDerivAt_id u).const_mul (r - 1))).const_mul ((r - v) / (2 * r)))
  convert! h using 1
  dsimp [comparisonKernelDeriv]
  ring

theorem comparisonKernelDeriv_hasDerivAt (v m r u : ℝ) :
    HasDerivAt (comparisonKernelDeriv v m r) (comparisonKernelDeriv2 v m r u) u := by
  have h := ((((Real.hasDerivAt_sinh (m * u)).comp u
    ((hasDerivAt_id u).const_mul m)).const_mul m).sub
    (((Real.hasDerivAt_sinh ((r + 1) * u)).comp u
      ((hasDerivAt_id u).const_mul (r + 1))).const_mul (((v + r) / (2 * r)) * (r + 1)))).sub
    (((Real.hasDerivAt_sinh ((r - 1) * u)).comp u
      ((hasDerivAt_id u).const_mul (r - 1))).const_mul (((r - v) / (2 * r)) * (r - 1)))
  convert! h using 1
  dsimp [comparisonKernelDeriv2]
  ring

theorem comparisonKernel_jet {d v m r : ℝ} (hd : 0 ≤ d) (hdr : d < r)
    (hm : m ^ 2 = d ^ 2 + 2 * v + 1) :
    comparisonKernel v m r 0 = 0 ∧ comparisonKernelDeriv v m r 0 = 0 ∧
      comparisonKernelDeriv2 v m r 0 < 0 := by
  have hr : 0 < r := hd.trans_lt hdr
  have hrne : r ≠ 0 := ne_of_gt hr
  have heq : comparisonKernel v m r 0 = 0 := by
    unfold comparisonKernel
    simp only [mul_zero, Real.cosh_zero, mul_one]
    field_simp
    ring
  have heq' : comparisonKernelDeriv v m r 0 = 0 := by
    simp only [comparisonKernelDeriv, mul_zero, Real.sinh_zero, sub_self]
  have heq'' : comparisonKernelDeriv2 v m r 0 = d ^ 2 - r ^ 2 := by
    simp only [comparisonKernelDeriv2, mul_zero, Real.cosh_zero, mul_one]
    rw [hm]
    field_simp
    ring
  exact ⟨heq, heq', heq'' ▸ (by nlinarith)⟩

theorem comparisonKernel_negative_near_zero {d v m r : ℝ} (hd : 0 ≤ d) (hdr : d < r)
    (hm : m ^ 2 = d ^ 2 + 2 * v + 1) :
    ∃ e : ℝ, 0 < e ∧ ∀ u ∈ Ioc 0 e, comparisonKernel v m r u < 0 := by
  obtain ⟨h0, h0', h0''⟩ := comparisonKernel_jet hd hdr hm
  exact negative_near_zero_of_second_derivative (comparisonKernel_hasDerivAt v m r)
    (comparisonKernelDeriv_hasDerivAt v m r)
    (by unfold comparisonKernelDeriv2; fun_prop) h0 h0' h0''

theorem comparisonKernel_integrable (v m r : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u => Real.exp (-x * Real.cosh u) * comparisonKernel v m r u) (Ioi 0) := by
  have hm := (besselIntegrand_integrable m hx).integrableOn (s := Ioi (0 : ℝ))
  have hp := ((besselIntegrand_integrable (r + 1) hx).integrableOn (s := Ioi (0 : ℝ))).const_mul
    ((v + r) / (2 * r))
  have hn := ((besselIntegrand_integrable (r - 1) hx).integrableOn (s := Ioi (0 : ℝ))).const_mul
    ((r - v) / (2 * r))
  convert (hm.sub hp).sub hn using 1
  ext u
  dsimp [besselIntegrand, comparisonKernel]
  ring

end GauntIntegral
