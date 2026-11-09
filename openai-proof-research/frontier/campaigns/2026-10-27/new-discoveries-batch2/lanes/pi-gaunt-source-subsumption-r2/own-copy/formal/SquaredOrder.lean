import Mathlib

set_option autoImplicit false
set_option warningAsError true

open Set
noncomputable section

namespace GauntIntegral

def orderKernel (u a : ℝ) : ℝ := Real.cosh (u * Real.sqrt a)

def orderTerm (u a : ℝ) (k : ℕ) : ℝ :=
  u ^ (2 * k) / (2 * k).factorial * a ^ k

theorem orderKernel_hasSum (u : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    HasSum (orderTerm u a) (orderKernel u a) := by
  have heq : orderTerm u a =
      fun k : ℕ => (u * Real.sqrt a) ^ (2 * k) / (2 * k).factorial := by
    funext k
    simp only [orderTerm, mul_pow, pow_mul, Real.sq_sqrt ha]
    ring
  rw [heq]
  exact Real.hasSum_cosh _

theorem orderTerm_convex (u : ℝ) (k : ℕ) :
    ConvexOn ℝ (Ici 0) (fun a : ℝ => orderTerm u a k) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro a ha b hb s t hs ht hst
  have hp := (convexOn_pow (𝕜 := ℝ) k).2 ha hb hs ht hst
  have hc : 0 ≤ u ^ (2 * k) / ((2 * k).factorial : ℝ) := by
    apply div_nonneg
    · rw [pow_mul]
      exact pow_nonneg (sq_nonneg u) k
    · positivity
  simpa only [orderTerm, smul_eq_mul, mul_add, mul_assoc, mul_left_comm]
    using mul_le_mul_of_nonneg_left hp hc

theorem orderKernel_strictConvex {u : ℝ} (hu : u ≠ 0) :
    StrictConvexOn ℝ (Ici 0) (orderKernel u) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro a ha b hb hab s t hs ht hst
  have ha0 : 0 ≤ a := ha
  have hb0 : 0 ≤ b := hb
  have hm : 0 ≤ s * a + t * b := by positivity
  have hsum := orderKernel_hasSum u hm
  have hsum' := ((orderKernel_hasSum u ha).mul_left s).add
    ((orderKernel_hasSum u hb).mul_left t)
  have hle : ∀ k : ℕ, orderTerm u (s * a + t * b) k ≤
      s * orderTerm u a k + t * orderTerm u b k := by
    intro k
    exact (orderTerm_convex u k).2 ha hb (le_of_lt hs) (le_of_lt ht) hst
  have hstrict : orderTerm u (s * a + t * b) 2 <
      s * orderTerm u a 2 + t * orderTerm u b 2 := by
    have hp := (strictConvexOn_pow (n := 2) (by omega)).2 ha hb hab hs ht hst
    have hc : 0 < u ^ (2 * 2) / ((2 * 2).factorial : ℝ) := by
      apply div_pos
      · rw [pow_mul]
        exact pow_pos (sq_pos_of_ne_zero hu) 2
      · positivity
    have h := mul_lt_mul_of_pos_left hp hc
    simpa only [orderTerm, smul_eq_mul, mul_add, mul_assoc, mul_left_comm] using h
  have h := Summable.tsum_lt_tsum hle hstrict hsum.summable hsum'.summable
  simpa only [hsum.tsum_eq, hsum'.tsum_eq, smul_eq_mul] using h

theorem orderKernel_extrapolation {u d v : ℝ} (hu : u ≠ 0)
    (hd : 0 < d) (hdv : d < v) :
    (v + d) * orderKernel u ((d + 1) ^ 2) +
      (d - v) * orderKernel u ((d - 1) ^ 2) <
        (2 * d) * orderKernel u (d ^ 2 + 2 * v + 1) := by
  have hv : 0 < v := lt_trans hd hdv
  have hc : 0 ≤ d ^ 2 + 2 * v + 1 := by positivity
  have hab : (d - 1) ^ 2 < (d + 1) ^ 2 := by nlinarith
  have hbc : (d + 1) ^ 2 < d ^ 2 + 2 * v + 1 := by nlinarith
  have h := (orderKernel_strictConvex hu).secant_strict_mono_aux1
    (show (d - 1) ^ 2 ∈ Ici (0 : ℝ) by simpa only [mem_Ici] using sq_nonneg (d - 1))
    (show d ^ 2 + 2 * v + 1 ∈ Ici (0 : ℝ) by simpa only [mem_Ici] using hc) hab hbc
  nlinarith

theorem orderKernel_hasDerivAt_one (u : ℝ) :
    HasDerivAt (orderKernel u) (u * Real.sinh u / 2) 1 := by
  unfold orderKernel
  convert! (Real.hasDerivAt_cosh (u * Real.sqrt 1)).comp 1
    ((Real.hasDerivAt_sqrt (x := 1) (by norm_num)).const_mul u) using 1
  norm_num
  ring

theorem orderKernel_tangent {u c : ℝ} (hu : u ≠ 0) (hc : 1 < c) :
    Real.cosh u + (c - 1) * (u * Real.sinh u / 2) < orderKernel u c := by
  have h := (orderKernel_strictConvex hu).lt_slope_of_hasDerivAt
    (show (1 : ℝ) ∈ Ici 0 by norm_num)
    (show c ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith) hc
    (orderKernel_hasDerivAt_one u)
  rw [slope_def_field] at h
  have hp : 0 < c - 1 := by linarith
  have h' := (lt_div_iff₀ hp).mp h
  simpa [orderKernel] using (show orderKernel u 1 +
    (c - 1) * (u * Real.sinh u / 2) < orderKernel u c by nlinarith)

end GauntIntegral
