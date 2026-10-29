import Crossing
set_option autoImplicit false
set_option warningAsError true
open Set Filter Topology
namespace BesselTransfer

 theorem ratio_positive {R W D : ℝ → ℝ}
    (hD : ∀ x > 0, 0 < D x)
    (hr : ∀ x > 0, HasDerivAt R (W x / D x) x)
    (hw : ∀ x > 0, 0 < W x) : StrictMonoOn R (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun x hx => (hr x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := interior_subset hx
    rw [(hr x hx').deriv]
    exact div_pos (hw x hx') (hD x hx')

 theorem ratio_peak {R W D : ℝ → ℝ} {c : ℝ}
    (hD : ∀ x > 0, 0 < D x)
    (hr : ∀ x > 0, HasDerivAt R (W x / D x) x)
    (hc : 0 < c) (hl : ∀ x, 0 < x → x < c → 0 < W x)
    (hu : ∀ x, c < x → W x < 0) :
    StrictMonoOn R (Ioc 0 c) ∧ StrictAntiOn R (Ici c) := by
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Ioc 0 c)
    · exact fun x hx => (hr x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Ioo 0 c := by simpa only [interior_Ioc] using hx
      rw [(hr x hx'.1).deriv]
      exact div_pos (hl x hx'.1 hx'.2) (hD x hx'.1)
  · apply strictAntiOn_of_deriv_neg (convex_Ici c)
    · exact fun x hx => (hr x (lt_of_lt_of_le hc hx)).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : c < x := by simpa only [interior_Ici, mem_Ioi] using hx
      rw [(hr x (hc.trans hx')).deriv]
      exact div_neg_of_neg_of_pos (hu x hx') (hD x (hc.trans hx'))

/-- Closed positive-initial-data transfer, valid for every real A and B≥0. -/
 theorem initial_transfer {R W p D : ℝ → ℝ} {A B : ℝ}
    (hB : 0 ≤ B) (hp : ∀ x > 0, 0 < p x)
    (hw : ∀ x > 0, HasDerivAt W ((A/x-B*x)*p x) x)
    (hi : InitiallyPositive W) (hD : ∀ x > 0, 0 < D x)
    (hr : ∀ x > 0, HasDerivAt R (W x / D x) x) : IncreasingOrPeak R := by
  rcases sign_dichotomy hB hp hw hi with h | ⟨c, hc, _, hl, hu⟩
  · exact Or.inl (ratio_positive hD hr h)
  · exact Or.inr ⟨c, hc, ratio_peak hD hr hc hl hu⟩

 theorem increasingOrPeak_unimodal {R : ℝ → ℝ} (h : IncreasingOrPeak R) : Unimodal R := by
  rcases h with h | ⟨c, hc, hl, hu⟩
  · exact Or.inl h.monotoneOn
  · exact Or.inr (Or.inr ⟨c, hc, hl.monotoneOn, hu.antitoneOn⟩)

 theorem potential_nonpositive {A B x : ℝ} (hA : A ≤ 0) (hB : 0 ≤ B)
    (hx : 0 < x) : A/x-B*x ≤ 0 := by
  exact sub_nonpos.mpr (le_trans (div_nonpos_of_nonpos_of_nonneg hA hx.le)
    (mul_nonneg hB hx.le))

 theorem W_antitone {W p : ℝ → ℝ} {A B : ℝ}
    (hA : A ≤ 0) (hB : 0 ≤ B) (hp : ∀ x > 0, 0 < p x)
    (hw : ∀ x > 0, HasDerivAt W ((A/x-B*x)*p x) x) : AntitoneOn W (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun x hx => (hw x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hw x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := interior_subset hx
    rw [(hw x hx').deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (potential_nonpositive hA hB hx') (hp x hx').le

 theorem nonpositive_of_zero_limit {W : ℝ → ℝ}
    (hm : AntitoneOn W (Ioi 0)) (hl : Tendsto W (𝓝[>] 0) (𝓝 0)) :
    ∀ x > 0, W x ≤ 0 := by
  intro x hx
  apply ge_of_tendsto hl
  filter_upwards [Ioo_mem_nhdsGT hx] with z hz
  exact hm hz.1 hx hz.2.le

/-- Zero endpoint data, for A≤0, gives a decreasing (possibly constant) ratio. -/
 theorem zero_limit_transfer {R W p D : ℝ → ℝ} {A B : ℝ}
    (hA : A ≤ 0) (hB : 0 ≤ B) (hp : ∀ x > 0, 0 < p x)
    (hw : ∀ x > 0, HasDerivAt W ((A/x-B*x)*p x) x)
    (hl : Tendsto W (𝓝[>] 0) (𝓝 0)) (hD : ∀ x > 0, 0 < D x)
    (hr : ∀ x > 0, HasDerivAt R (W x / D x) x) : AntitoneOn R (Ioi 0) := by
  have hn := nonpositive_of_zero_limit (W_antitone hA hB hp hw) hl
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun x hx => (hr x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hr x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := interior_subset hx
    rw [(hr x hx').deriv]
    exact div_nonpos_of_nonpos_of_nonneg (hn x hx') (hD x hx').le

/-- Direct source-facing generic endpoint, keeping all analytic bridges explicit. -/
 theorem unimodal_transfer {R W p D : ℝ → ℝ} {A B : ℝ}
    (hB : 0 ≤ B) (hp : ∀ x > 0, 0 < p x)
    (hw : ∀ x > 0, HasDerivAt W ((A/x-B*x)*p x) x)
    (hinit : InitiallyPositive W ∨ (A ≤ 0 ∧ Tendsto W (𝓝[>] 0) (𝓝 0)))
    (hD : ∀ x > 0, 0 < D x)
    (hr : ∀ x > 0, HasDerivAt R (W x / D x) x) : Unimodal R := by
  rcases hinit with hi | ⟨hA, hl⟩
  · exact increasingOrPeak_unimodal (initial_transfer hB hp hw hi hD hr)
  · exact Or.inr (Or.inl (zero_limit_transfer hA hB hp hw hl hD hr))

end BesselTransfer
