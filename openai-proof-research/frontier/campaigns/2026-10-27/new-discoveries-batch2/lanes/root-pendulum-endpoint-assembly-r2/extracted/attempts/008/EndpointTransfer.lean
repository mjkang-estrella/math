module
public import EndpointContinuity
public import Mathlib.Analysis.Convex.Continuous
public section
noncomputable section
open Real MeasureTheory Set Filter
open scoped Topology
namespace PendulumTimeMap
theorem sourceTime_continuousOn_of_interior_convex {phi : ℝ}
 (hp : 0<phi) (hp1 : phi<Real.pi/2)
 (hc : ConvexOn ℝ (Ioo 0 2) (sourceTime phi)) :
 ContinuousOn (sourceTime phi) (Icc 0 2) := by
 intro z hz
 by_cases h0 : z=0
 · subst z; exact sourceTime_continuousWithinAt_zero hp hp1
 by_cases h2 : z=2
 · subst z; exact (sourceTime_continuousAt_two hp hp1).continuousWithinAt
 have hz' : z∈Ioo 0 2 := ⟨lt_of_le_of_ne hz.1 (Ne.symm h0),lt_of_le_of_ne hz.2 h2⟩
 exact ((hc.continuousOn isOpen_Ioo z hz').continuousAt (Ioo_mem_nhds hz'.1 hz'.2)).continuousWithinAt
theorem convexOn_Icc_of_interior {f : ℝ → ℝ}
 (hc : ConvexOn ℝ (Ioo 0 2) f) (hf : ContinuousOn f (Icc 0 2)) :
 ConvexOn ℝ (Icc 0 2) f := by
 refine ⟨convex_Icc 0 2, ?_⟩
 intro x hx y hy u v hu hv huv
 let c : ℝ → ℝ → ℝ := fun t q => (1-t)*q+t
 have cmem : ∀ q∈Icc (0:ℝ) 2, ∀ t∈Ioo (0:ℝ) 1, c t q∈Ioo 0 2 := by
   intro q hq t ht
   dsimp [c]
   constructor <;> nlinarith [hq.1,hq.2,ht.1,ht.2]
 have hm : u*x+v*y∈Icc (0:ℝ) 2 := by
   simpa only [smul_eq_mul] using (convex_Icc (0:ℝ) 2 hx hy hu hv huv)
 have hlim : ∀ q∈Icc (0:ℝ) 2,
   Tendsto (fun t => f (c t q)) (𝓝[Ioi 0] 0) (𝓝 (f q)) := by
   intro q hq
   apply (hf q hq).tendsto.comp
   apply tendsto_nhdsWithin_iff.mpr
   constructor
   · have h : Continuous (fun t => c t q) := by dsimp [c]; fun_prop
     simpa [c] using h.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
   · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with t ht ht1
     exact ⟨(cmem q hq t ⟨ht,ht1⟩).1.le,(cmem q hq t ⟨ht,ht1⟩).2.le⟩
 have he : ∀ t, c t (u*x+v*y)=u*c t x+v*c t y := by
   intro t
   dsimp [c]
   nlinarith [huv]
 have hle : ∀ᶠ t in 𝓝[Ioi (0:ℝ)] 0, f (c t (u*x+v*y))≤u*f (c t x)+v*f (c t y) := by
   filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with t ht ht1
   rw [he t]
   exact hc.2 (cmem x hx t ⟨ht,ht1⟩) (cmem y hy t ⟨ht,ht1⟩) hu hv huv
 exact le_of_tendsto_of_tendsto (hlim _ hm) (((hlim _ hx).const_mul u).add ((hlim _ hy).const_mul v)) hle
theorem sourceClaim_of_interior_convex :
 (∀ phi : ℝ, 0<phi → phi<Real.pi/2 → ConvexOn ℝ (Ioo 0 2) (sourceTime phi)) →
 SourceClaim := by
 intro hc phi hp hp1
 exact convexOn_Icc_of_interior (hc phi hp hp1)
   (sourceTime_continuousOn_of_interior_convex hp hp1 (hc phi hp hp1))
end PendulumTimeMap
