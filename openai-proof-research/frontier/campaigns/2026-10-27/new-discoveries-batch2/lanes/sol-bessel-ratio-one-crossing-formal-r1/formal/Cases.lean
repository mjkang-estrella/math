import Transfer
set_option autoImplicit false
set_option warningAsError true
open Set Filter Topology
namespace BesselTransfer

 theorem unique_zero {W p : ℝ → ℝ} {A B : ℝ}
    (hB : 0 ≤ B) (hp : ∀ x > 0, 0 < p x)
    (hw : ∀ x > 0, HasDerivAt W ((A/x-B*x)*p x) x)
    (hi : InitiallyPositive W) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hcz : W c = 0) (hdz : W d = 0) : c = d := by
  rcases lt_trichotomy c d with h | h | h
  · have := forward_crossing hB hp hw hi hc hcz.le h
    simp only [hcz, hdz, lt_self_iff_false] at this
  · exact h
  · have := forward_crossing hB hp hw hi hd hdz.le h
    simp only [hcz, hdz, lt_self_iff_false] at this

/-- Equal-scale A≥0 cases cannot have a peak under positive initial data. -/
 theorem equal_scale_increasing {R W p D : ℝ → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (hp : ∀ x > 0, 0 < p x)
    (hw : ∀ x > 0, HasDerivAt W ((A/x-0*x)*p x) x)
    (hi : InitiallyPositive W) (hD : ∀ x > 0, 0 < D x)
    (hr : ∀ x > 0, HasDerivAt R (W x / D x) x) : StrictMonoOn R (Ioi 0) := by
  apply ratio_positive hD hr
  intro x hx
  exact positive_of_coeff_nonneg (by norm_num) hp hw hi hx
    (by simpa only [zero_mul, sub_zero] using div_nonneg hA hx.le)

 theorem strict_zero_limit_transfer {R W p D : ℝ → ℝ} {A B : ℝ}
    (hA : A ≤ 0) (hB : 0 ≤ B) (hstrict : A < 0 ∨ 0 < B)
    (hp : ∀ x > 0, 0 < p x)
    (hw : ∀ x > 0, HasDerivAt W ((A/x-B*x)*p x) x)
    (hl : Tendsto W (𝓝[>] 0) (𝓝 0)) (hD : ∀ x > 0, 0 < D x)
    (hr : ∀ x > 0, HasDerivAt R (W x / D x) x) : StrictAntiOn R (Ioi 0) := by
  have hm : StrictAntiOn W (Ioi 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    · exact fun x hx => (hw x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 < x := interior_subset hx
      rw [(hw x hx').deriv]
      apply mul_neg_of_neg_of_pos _ (hp x hx')
      rcases hstrict with h | h
      · exact sub_neg.mpr (lt_of_lt_of_le (div_neg_of_neg_of_pos h hx') (mul_nonneg hB hx'.le))
      · exact sub_neg.mpr (lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg hA hx'.le) (mul_pos h hx'))
  have hn := nonpositive_of_zero_limit hm.antitoneOn hl
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact fun x hx => (hr x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := interior_subset hx
    have hn' : W x < 0 := lt_of_lt_of_le
      (hm (show 0 < x/2 by linarith) hx' (by linarith))
      (hn (x/2) (by linarith))
    rw [(hr x hx').deriv]
    exact div_neg_of_neg_of_pos hn' (hD x hx')

 theorem constant_zero_limit_transfer {R W D : ℝ → ℝ}
    (hw : ∀ x > 0, HasDerivAt W 0 x)
    (hl : Tendsto W (𝓝[>] 0) (𝓝 0))
    (hr : ∀ x > 0, HasDerivAt R (W x / D x) x) :
    ∀ x > 0, ∀ y > 0, R x = R y := by
  have hwa : AntitoneOn W (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · exact fun x hx => (hw x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hw x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · exact fun x hx => le_of_eq (hw x (interior_subset hx)).deriv
  have hwm : MonotoneOn W (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact fun x hx => (hw x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hw x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · exact fun x hx => le_of_eq (hw x (interior_subset hx)).deriv.symm
  have hwzero : ∀ x > 0, W x = 0 := by
    intro x hx
    apply le_antisymm (nonpositive_of_zero_limit hwa hl x hx)
    apply le_of_tendsto hl
    filter_upwards [Ioo_mem_nhdsGT hx] with z hz
    exact hwm hz.1 hx hz.2.le
  have hrd : ∀ x > 0, HasDerivAt R 0 x := by
    intro x hx
    simpa only [hwzero x hx, zero_div] using hr x hx
  have hm : MonotoneOn R (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact fun x hx => (hrd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hrd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · exact fun x hx => le_of_eq (hrd x (interior_subset hx)).deriv.symm
  have ha : AntitoneOn R (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · exact fun x hx => (hrd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hrd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · exact fun x hx => le_of_eq (hrd x (interior_subset hx)).deriv
  intro x hx y hy
  rcases le_total x y with h | h
  · exact le_antisymm (hm hx hy h) (ha hx hy h)
  · exact le_antisymm (ha hy hx h) (hm hy hx h)

end BesselTransfer
