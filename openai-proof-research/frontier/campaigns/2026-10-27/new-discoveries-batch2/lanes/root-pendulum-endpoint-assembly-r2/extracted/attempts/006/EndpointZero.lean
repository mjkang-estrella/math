module
public import ClosedSubstitution
public import EndpointTwo
public section
noncomputable section
open Real MeasureTheory Set Filter
open scoped Topology
namespace PendulumTimeMap
theorem source_integrable_zero {phi : ℝ} (hp : 0<phi) (hp1 : phi<Real.pi/2) :
 IntervalIntegrable (sourceKernel phi 0) volume 0 phi := by
 have ha := a_range hp hp1
 let w : ℝ → ℝ := fun t => (Real.sqrt (2-t))⁻¹
 have hw : ContinuousOn w (Icc 0 (change (a phi) (Real.pi/2))) := by
   apply ContinuousOn.inv₀
   · exact (continuous_const.sub continuous_id).sqrt.continuousOn
   · intro t ht
     have he : change (a phi) (Real.pi/2)=a phi := by simp [change,show 2*(Real.pi/2)=Real.pi by ring]; ring
     rw [he] at ht
     exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [ht.2]))
 have h := (closed_weighted_substitution ha.1 (by positivity : 0<Real.pi/2) le_rfl w hw).1
 have he : change (a phi) (Real.pi/2)=a phi := by simp [change,show 2*(Real.pi/2)=Real.pi by ring]; ring
 rw [he] at h
 have ht : IntervalIntegrable (transformedKernel (a phi) 0) volume 0 (a phi) := by
   apply h.congr_uIoo
   rw [uIoo_of_lt ha.1]
   intro t ht
   dsimp [w,transformedKernel]
   rw [show t*(2-t)*(a phi+0-t)=(t*(a phi-t))*(2-t) by ring]
   rw [Real.sqrt_mul (show 0≤t*(a phi-t) by nlinarith [ht.1,ht.2])]
   ring
 have hd : ∀ x∈Ioo (min 0 phi) (max 0 phi),
   HasDerivAt (change 2) (changeDeriv 2 x) x := fun x _ => change_deriv 2 x
 have hn : ∀ x∈Ioo (min 0 phi) (max 0 phi), 0≤changeDeriv 2 x := by
   simp only [min_eq_left hp.le,max_eq_right hp.le]
   intro x hx
   unfold changeDeriv
   exact le_of_lt (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi
     (by linarith [hx.1]) (by linarith [hx.2])))
 have hh := (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
   (g := transformedKernel (a phi) 0) (change_cont 2).continuousOn hd hn).mpr
 have hz : change 2 0=0 := by simp [change]
 rw [hz,change_two] at hh
 have hi := hh ht
 have heq : EqOn (fun x => transformedKernel (a phi) 0 (change 2 x)*changeDeriv 2 x)
   (fun x => 2*sourceKernel phi 0 x) (uIoo 0 phi) := by
   rw [uIoo_of_lt hp]
   intro x hx
   have hs := change_sqrt (c := 2) (by norm_num) hp1 hx
   have hspos : Real.sin (2*x)≠0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
     (by linarith [hx.1]) (by linarith [hx.2]))
   dsimp [transformedKernel]
   rw [Real.sqrt_mul (show 0≤change 2 x*(2-change 2 x) by
     have hr := change_range (c := 2) (by norm_num) hp1 ⟨hx.1.le,hx.2.le⟩
     rw [change_two phi] at hr
     exact mul_nonneg hr.1 (by linarith [hr.2]))]
   rw [hs]
   dsimp [sourceKernel,changeDeriv,change,a]
   have heq : 1-cos (2*phi)+0-(2/2*(1-cos (2*x))) = 0-cos (2*phi)+cos (2*x) := by ring
   rw [heq]
   field_simp [hspos]
   <;> ring
 have hi2 := hi.congr_uIoo heq
 have := hi2.const_mul (1/2:ℝ)
 convert this using 1
 ext x
 ring
end PendulumTimeMap
