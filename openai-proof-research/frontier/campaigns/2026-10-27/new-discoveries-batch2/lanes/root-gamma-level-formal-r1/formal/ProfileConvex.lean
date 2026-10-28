import GammaDefs

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open Set Filter Topology
namespace GammaLevel

def profileSlope (u : ℝ) : ℝ := -2 / (u * (u ^ 2 - 1))

theorem profile_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt profile (profileSlope u) u := by
  have hu0 : u ≠ 0 := ne_of_gt (lt_trans zero_lt_one hu)
  have hs : 0 < u ^ 2 - 1 := by nlinarith
  have hi : 0 < 1 - u⁻¹ ^ 2 := by
    have hi0 : 0 < u⁻¹ := inv_pos.mpr (by linarith)
    have hi1 : u⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hu
    nlinarith
  have hd := (((hasDerivAt_id u).inv hu0).pow 2).const_sub 1
  have hl := (hd.log (ne_of_gt hi)).neg
  change HasDerivAt (fun y => -Real.log (1 - y⁻¹ ^ 2)) (profileSlope u) u
  convert hl using 1
  · rfl
  · dsimp [profileSlope]
    field_simp

theorem profileSlope_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt profileSlope
      (2 * (3 * u ^ 2 - 1) / (u ^ 2 * (u ^ 2 - 1) ^ 2)) u := by
  have hu0 : u ≠ 0 := ne_of_gt (lt_trans zero_lt_one hu)
  have hs : u ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith : 0 < u ^ 2 - 1)
  have hd := (hasDerivAt_id u).mul (((hasDerivAt_id u).pow 2).sub_const 1)
  have h := (hasDerivAt_const u (-2 : ℝ)).div hd (mul_ne_zero hu0 hs)
  change HasDerivAt (fun y => -2 / (y * (y ^ 2 - 1))) _ u
  convert h using 1
  · rfl
  · dsimp
    field_simp
    ring

theorem profile_strictConvexOn : StrictConvexOn ℝ (Ioi 1) profile := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 1)
  · intro u hu
    exact (profile_hasDerivAt hu).continuousAt.continuousWithinAt
  · intro u hu
    change 1 < u at hu
    have hd : deriv profile =ᶠ[𝓝 u] profileSlope := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
      exact (profile_hasDerivAt hv).deriv
    have hdd := (profileSlope_hasDerivAt hu).congr_of_eventuallyEq hd
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
    rw [hdd.deriv]
    apply div_pos
    · nlinarith [show 0 < u ^ 2 - 1 by nlinarith [hu]]
    · exact mul_pos (sq_pos_of_pos (by linarith [hu]))
        (sq_pos_of_pos (by nlinarith [hu] : 0 < u ^ 2 - 1))

end GammaLevel
