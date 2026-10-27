import Mathlib

open Filter Set
open scoped Topology

namespace DeTemple

noncomputable def boundaryModel (h : ℝ → ℝ) (a x : ℝ) : ℝ :=
  24 * (x ^ 4 + a * x ^ 2) * (h x - Real.log x) - x ^ 2

noncomputable def regularPart (h : ℝ → ℝ) (a x : ℝ) : ℝ :=
  (81 * x ^ 2 + 9 * a) * h (3 * x) -
    2 * (16 * x ^ 2 + 4 * a) * h (2 * x) + (x ^ 2 + a) * h x -
    (81 * x ^ 2 + 9 * a) * Real.log 3 +
    2 * (16 * x ^ 2 + 4 * a) * Real.log 2

theorem difference_identity (h : ℝ → ℝ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    (boundaryModel h a (3 * x) - 2 * boundaryModel h a (2 * x) +
      boundaryModel h a x) / x ^ 2 =
      24 * (regularPart h a x + (-Real.log x) * (50 * x ^ 2 + 2 * a)) - 2 := by
  unfold boundaryModel regularPart
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hx),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx)]
  field_simp
  ring

theorem normalized_difference_tendsto (h : ℝ → ℝ) (hh : ContinuousAt h 0)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x => (boundaryModel h a (3 * x) - 2 * boundaryModel h a (2 * x) +
      boundaryModel h a x) / x ^ 2) (𝓝[>] (0 : ℝ)) atTop := by
  have h3 : ContinuousAt (fun x : ℝ => h (3 * x)) 0 := by
    exact hh.comp_of_eq (f := fun x : ℝ => 3 * x) (by fun_prop) (by simp)
  have h2 : ContinuousAt (fun x : ℝ => h (2 * x)) 0 := by
    exact hh.comp_of_eq (f := fun x : ℝ => 2 * x) (by fun_prop) (by simp)
  have hr : ContinuousAt (regularPart h a) 0 := by
    unfold regularPart
    have hA : ContinuousAt (fun x : ℝ => 81 * x ^ 2 + 9 * a) 0 := by fun_prop
    have hB : ContinuousAt (fun x : ℝ => 16 * x ^ 2 + 4 * a) 0 := by fun_prop
    have hC : ContinuousAt (fun x : ℝ => x ^ 2 + a) 0 := by fun_prop
    exact ((((hA.mul h3).sub ((continuousAt_const.mul hB).mul h2)).add
      (hC.mul hh)).sub (hA.mul continuousAt_const)).add
      ((continuousAt_const.mul hB).mul continuousAt_const)
  have hp : Tendsto (fun x : ℝ => 50 * x ^ 2 + 2 * a)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * a)) := by
    have hc : ContinuousAt (fun x : ℝ => 50 * x ^ 2 + 2 * a) 0 := by fun_prop
    have ht := hc.tendsto
    rw [show 50 * (0 : ℝ) ^ 2 + 2 * a = 2 * a by ring] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun x : ℝ => -Real.log x) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hm := hl.atTop_mul_pos (by positivity : 0 < 2 * a) hp
  have hs := (hr.tendsto.mono_left nhdsWithin_le_nhds).add_atTop hm
  have ht := (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 24) hs).atTop_add
    (tendsto_const_nhds (x := (-2 : ℝ)))
  simp only [← sub_eq_add_neg] at ht
  apply ht.congr'
  filter_upwards [eventually_mem_nhdsWithin] with x hx
  exact (difference_identity h a hx).symm

theorem exists_boundary_midpoint (h : ℝ → ℝ) (hh : ContinuousAt h 0)
    {a : ℝ} (ha : 0 < a) :
    ∃ x : ℝ, 0 < x ∧ boundaryModel h a (2 * x) <
      (boundaryModel h a x + boundaryModel h a (3 * x)) / 2 := by
  have he := (normalized_difference_tendsto h hh ha).eventually_gt_atTop 0
  have hp : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < x := eventually_mem_nhdsWithin
  obtain ⟨x, hx, hv⟩ := (hp.and he).exists
  refine ⟨x, hx, ?_⟩
  have hd := (div_pos_iff_of_pos_right (sq_pos_of_pos hx)).mp hv
  linarith

end DeTemple
