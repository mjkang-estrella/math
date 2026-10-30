module
public import Substitution
public section
noncomputable section
open Real MeasureTheory Set
namespace PendulumTimeMap
theorem change_two (x : ℝ) : change 2 x=a x := by unfold change a; ring
theorem source_piece {phi z q : ℝ} (hq0 : 0<q) (hq : q<Real.pi/2)
 (hbound : a q<a phi+z) :
 IntervalIntegrable (sourceKernel phi z) volume 0 q ∧
 IntervalIntegrable (transformedKernel (a phi) z) volume 0 (a q) ∧
 (∫ t in 0..a q, transformedKernel (a phi) z t)=
 2*(∫ x in 0..q, sourceKernel phi z x) := by
 let s := a phi+z
 let w : ℝ → ℝ := fun t => (Real.sqrt (s-t))⁻¹
 have hw : ContinuousOn w (Icc 0 (change 2 q)) := by
   apply ContinuousOn.inv₀
   · exact (continuous_const.sub continuous_id).sqrt.continuousOn
   · intro t ht
     apply ne_of_gt
     apply Real.sqrt_pos.mpr
     rw [change_two] at ht
     dsimp [s]
     linarith [ht.2]
 have h := weighted_substitution (c := 2) (by norm_num) hq0 hq w hw
 have hr := a_range hq0 hq
 have he : EqOn (fun t => w t / Real.sqrt (t*(2-t))) (transformedKernel (a phi) z) (Icc 0 (a q)) := by
   intro t ht
   dsimp [w, s, transformedKernel]
   rw [Real.sqrt_mul (mul_nonneg ht.1 (by linarith [ht.2]))]
   ring
 have hsource : (fun x => w (change 2 x))=sourceKernel phi z := by
   funext x
   dsimp [w,s,change,sourceKernel,a]
   congr 2
   ring
 rw [change_two] at h
 have hwc : ContinuousOn (fun x => w (change 2 x)) (Icc 0 q) :=
   hw.comp (change_cont 2).continuousOn (fun x hx => change_range (by norm_num) hq hx)
 rw [hsource] at hwc
 refine ⟨hwc.intervalIntegrable_of_Icc hq0.le, ?_, ?_⟩
 · apply h.1.congr_uIoo
   intro t ht
   rw [uIoo_of_lt hr.1] at ht
   exact he ⟨ht.1.le,ht.2.le⟩
 · rw [← intervalIntegral.integral_congr (by simpa [uIcc_of_le hr.1.le] using he), h.2, hsource]
theorem source_integrable {phi z : ℝ} (hp : 0<phi) (hp1 : phi<Real.pi/2)
 (hz : 0<z) (hz1 : z<2) :
 IntervalIntegrable (sourceKernel phi z) volume 0 phi ∧
 IntervalIntegrable (sourceKernel phi z) volume 0 (b z) := by
 have ha := a_range hp hp1
 have hb := b_range hz hz1
 exact ⟨(source_piece hp hp1 (by linarith)).1,
 (source_piece hb.1 hb.2 (by rw [a_b hz.le hz1.le]; linarith)).1⟩
theorem transformed_integrable {a z : ℝ} (ha : 0<a) (ha1 : a<2)
 (hz : 0<z) (hz1 : z<2) :
 IntervalIntegrable (transformedKernel a z) volume 0 a ∧
 IntervalIntegrable (transformedKernel a z) volume 0 z := by
 have hb := b_range ha ha1
 have h := source_piece (phi := b a) (z := z) hb.1 hb.2 (by linarith)
 have hbz := b_range hz hz1
 have k := source_piece (phi := b a) (z := z) hbz.1 hbz.2 (by
   rw [a_b ha.le ha1.le, a_b hz.le hz1.le]; linarith)
 simpa only [a_b ha.le ha1.le, a_b hz.le hz1.le] using And.intro h.2.1 k.2.1
theorem sourceTime_eq_transformedTime {phi z : ℝ} (hp : 0<phi) (hp1 : phi<Real.pi/2)
 (hz : 0<z) (hz1 : z<2) : sourceTime phi z=transformedTime (a phi) z := by
 have ha := a_range hp hp1
 have hb := b_range hz hz1
 have h := (source_piece (phi := phi) (z := z) hp hp1 (by linarith)).2.2
 have k := (source_piece (phi := phi) (z := z) hb.1 hb.2 (by rw [a_b hz.le hz1.le]; linarith)).2.2
 rw [a_b hz.le hz1.le] at k
 unfold sourceTime transformedTime
 rw [h,k]
 ring
end PendulumTimeMap
