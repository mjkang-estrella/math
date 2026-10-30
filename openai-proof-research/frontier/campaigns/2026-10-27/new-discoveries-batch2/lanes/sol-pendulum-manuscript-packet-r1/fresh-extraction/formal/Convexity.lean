module
public import Moments
public import Source
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public section
noncomputable section
open Real MeasureTheory Set
namespace PendulumTimeMap

@[expose] def weight (n : ℕ) : ℝ := (Nat.choose (2*n) n : ℝ) / 8^n

theorem weight_pos (n : ℕ) : 0 < weight n := by
 unfold weight
 exact div_pos (by exact_mod_cast Nat.choose_pos (by omega : n ≤ 2*n)) (by positivity)

theorem moment_zero_convex {a : ℝ} (ha : 0<a) :
 ConvexOn ℝ (Ioi 0) (moment 0 a) := by
 refine ⟨convex_Ioi 0, ?_⟩
 intro x hx y hy u v hu hv huv
 change 0<x at hx
 change 0<y at hy
 have hm : 0 < u*x+v*y := by
  have : 0<u ∨ 0<v := by by_contra h; push Not at h; linarith
  rcases this with h | h
  · nlinarith [mul_pos h hx, mul_nonneg hv hy.le]
  · nlinarith [mul_pos h hy, mul_nonneg hu hx.le]
 simp only [smul_eq_mul]
 rw [moment_zero ha hm, moment_zero ha hx, moment_zero ha hy]
 rw [← add_mul, huv, one_mul]

theorem moment_one_convex {a : ℝ} (ha : 0<a) :
 ConvexOn ℝ (Ioi 0) (moment 1 a) := by
 refine ⟨convex_Ioi 0, ?_⟩
 intro x hx y hy u v hu hv huv
 change 0<x at hx
 change 0<y at hy
 have hm : 0 < u*x+v*y := by
  have : 0<u ∨ 0<v := by by_contra h; push Not at h; linarith
  rcases this with h | h
  · nlinarith [mul_pos h hx, mul_nonneg hv hy.le]
  · nlinarith [mul_pos h hy, mul_nonneg hu hx.le]
 have hs := Real.strictConcaveOn_sqrt.concaveOn.2
  (show a*x ∈ Ici 0 by exact (mul_pos ha hx).le)
  (show a*y ∈ Ici 0 by exact (mul_pos ha hy).le) hu hv huv
 simp only [smul_eq_mul] at hs ⊢
 rw [moment_one ha hm, moment_one ha hx, moment_one ha hy]
 rw [show a*(u*x+v*y)=u*(a*x)+v*(a*y) by ring]
 have he : Real.pi*(a+(u*x+v*y))/2 =
  u*(Real.pi*(a+x)/2)+v*(Real.pi*(a+y)/2) := by
  calc
   _ = (u+v)*(Real.pi*a/2)+Real.pi*(u*x+v*y)/2 := by rw [huv]; ring
   _ = _ := by ring
 rw [he]
 linarith

theorem positivePart_rpow_convex {p : ℝ} (hp : 1≤p) (y : ℝ) :
 ConvexOn ℝ univ (fun z : ℝ => (max (z-y) 0)^p) := by
 refine ⟨convex_univ, ?_⟩
 intro x _ z _ u v hu hv huv
 simp only [smul_eq_mul]
 have hmax : max (u*x+v*z-y) 0 ≤ u*max (x-y) 0+v*max (z-y) 0 := by
  apply max_le
  · calc
     u*x+v*z-y = u*(x-y)+v*(z-y) := by nlinarith [congrArg (fun q : ℝ => q*y) huv]
     _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_max_left (x-y) 0) hu)
      (mul_le_mul_of_nonneg_left (le_max_left (z-y) 0) hv)
  · positivity
 have hpow := Real.rpow_le_rpow (le_max_right (u*x+v*z-y) 0) hmax (by linarith : 0≤p)
 exact hpow.trans ((convexOn_rpow hp).2
  (show max (x-y) 0 ∈ Ici 0 from le_max_right _ _)
  (show max (z-y) 0 ∈ Ici 0 from le_max_right _ _) hu hv huv)


theorem inv_sqrt_jensen {x y u v : ℝ} (hx : 0<x) (hy : 0<y)
 (hu : 0≤u) (hv : 0≤v) (huv : u+v=1) :
 (Real.sqrt (u*x+v*y))⁻¹ ≤ u*(Real.sqrt x)⁻¹+v*(Real.sqrt y)⁻¹ := by
 have hs := Real.strictConcaveOn_sqrt.concaveOn.2 hx.le hy.le hu hv huv
 simp only [smul_eq_mul] at hs
 have hpos : 0<u*Real.sqrt x+v*Real.sqrt y := by
  have h : 0<u ∨ 0<v := by by_contra h; push Not at h; linarith
  rcases h with h | h
  · exact add_pos_of_pos_of_nonneg (mul_pos h (Real.sqrt_pos.mpr hx)) (by positivity)
  · exact add_pos_of_nonneg_of_pos (by positivity) (mul_pos h (Real.sqrt_pos.mpr hy))
 have hi := (convexOn_zpow (𝕜 := ℝ) (-1)).2
  (Real.sqrt_pos.mpr hx) (Real.sqrt_pos.mpr hy) hu hv huv
 simp only [smul_eq_mul, zpow_neg_one] at hi
 exact (inv_anti₀ hpos hs).trans hi

theorem momentKernel_rpow {n : ℕ} (hn : 1≤n) {a z t : ℝ}
 (ht : 0≤t) (hs : 0<a+z-t) :
 momentKernel n a z t = t^((n:ℝ)-1/2) / Real.sqrt (a+z-t) := by
 unfold momentKernel
 rw [Real.sqrt_mul ht]
 by_cases ht0 : t=0
 · subst t
   have hn' : (0:ℝ)<(n:ℝ)-1/2 := by
    have : (1:ℝ)≤n := by exact_mod_cast hn
    linarith
   rw [Real.zero_rpow (ne_of_gt hn')]
   simp [show n≠0 by omega]
 · have ht' : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
   rw [Real.rpow_sub ht', Real.rpow_natCast, ← Real.sqrt_eq_rpow]
   ring

@[expose] def movingKernel (n : ℕ) (a z y : ℝ) : ℝ :=
 (max (z-y) 0)^((n:ℝ)-1/2) / Real.sqrt (a+y)

theorem movingKernel_convex {n : ℕ} (hn : 2≤n) (a y : ℝ) :
 ConvexOn ℝ univ (fun z => movingKernel n a z y) := by
 have hp : (1:ℝ)≤(n:ℝ)-1/2 := by
  have : (2:ℝ)≤n := by exact_mod_cast hn
  linarith
 simpa only [movingKernel, smul_eq_mul, div_eq_mul_inv, mul_comm] using
  (positivePart_rpow_convex hp y).smul (inv_nonneg.mpr (Real.sqrt_nonneg (a+y)))

theorem movingKernel_eq_zero {n : ℕ} (hn : 1≤n) {a z y : ℝ} (hy : z≤y) :
 movingKernel n a z y=0 := by
 have hp : (n:ℝ)-1/2≠0 := by
  have : (1:ℝ)≤n := by exact_mod_cast hn
  linarith
 unfold movingKernel
 rw [max_eq_right (sub_nonpos.mpr hy), Real.zero_rpow hp, zero_div]

theorem movingKernel_eq_momentKernel {n : ℕ} (hn : 1≤n) {a z y : ℝ}
 (ha : 0<a) (hy : 0≤y) (hyz : y≤z) :
 movingKernel n a z y=momentKernel n a z (z-y) := by
 rw [momentKernel_rpow hn (sub_nonneg.mpr hyz) (by linarith)]
 unfold movingKernel
 rw [max_eq_left (sub_nonneg.mpr hyz)]
 congr 2; ring


theorem movingKernel_continuousOn {n : ℕ} (hn : 1≤n) {a z L : ℝ} (ha : 0<a) :
 ContinuousOn (movingKernel n a z) (Icc 0 L) := by
 have hp : (0:ℝ)≤(n:ℝ)-1/2 := by
  have : (1:ℝ)≤n := by exact_mod_cast hn
  linarith
 unfold movingKernel
 apply ContinuousOn.div
 · exact ((Real.continuous_rpow_const hp).comp
    ((continuous_const.sub continuous_id).max continuous_const)).continuousOn
 · exact (continuous_const.add continuous_id).sqrt.continuousOn
 · intro y hy
   exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hy.1]))

theorem moving_integral_truncated {n : ℕ} (hn : 1≤n) {a z L : ℝ}
 (ha : 0<a) (hz : 0<z) (hL : z≤L) :
 (∫ t in 0..z, momentKernel n a z t) = ∫ y in 0..L, movingKernel n a z y := by
 have hc := movingKernel_continuousOn (z := z) (L := L) hn ha
 have h1 := (movingKernel_continuousOn (z := z) (L := z) hn ha).intervalIntegrable_of_Icc (μ := volume) hz.le
 have h2 : IntervalIntegrable (movingKernel n a z) volume z L :=
  (hc.mono (Icc_subset_Icc hz.le le_rfl)).intervalIntegrable_of_Icc (μ := volume) hL
 have he : (∫ y in z..L, movingKernel n a z y)=0 := by
  calc
   _ = ∫ _y in z..L, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hL] at hy
    exact movingKernel_eq_zero hn hy.1
   _ = 0 := by simp
 rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, he, add_zero]
 have hs := intervalIntegral.integral_comp_sub_left (momentKernel n a z) (a := 0) (b := z) z
 simp only [sub_self, sub_zero] at hs
 rw [← hs]
 apply intervalIntegral.integral_congr
 intro y hy
 rw [uIcc_of_le hz.le] at hy
 exact (movingKernel_eq_momentKernel hn ha hy.1 hy.2).symm

theorem fixed_integral_convex (n : ℕ) {a : ℝ} (ha : 0<a) :
 ConvexOn ℝ (Ioi 0) (fun z => ∫ t in 0..a, momentKernel n a z t) := by
 refine ⟨convex_Ioi 0, ?_⟩
 intro x hx y hy u v hu hv huv
 change 0<x at hx
 change 0<y at hy
 have hm : 0<u*x+v*y := (convex_Ioi (0:ℝ)) hx hy hu hv huv
 have hix := (moment_integrable n ha hx).1
 have hiy := (moment_integrable n ha hy).1
 have him := (moment_integrable n ha hm).1
 simp only [smul_eq_mul] at hm ⊢
 rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
  ← intervalIntegral.integral_add (hix.const_mul u) (hiy.const_mul v)]
 apply intervalIntegral.integral_mono_on_of_le_Ioo ha.le him ((hix.const_mul u).add (hiy.const_mul v))
 intro t ht
 have ht0 : 0<t := ht.1
 have hta : t<a := ht.2
 unfold momentKernel
 rw [Real.sqrt_mul ht.1.le, Real.sqrt_mul ht.1.le, Real.sqrt_mul ht.1.le]
 have hi := inv_sqrt_jensen (x := a+x-t) (y := a+y-t) (by linarith [ht.2]) (by linarith [ht.2]) hu hv huv
 rw [show u*(a+x-t)+v*(a+y-t)=a+(u*x+v*y)-t by
  calc
   _ = (u+v)*(a-t)+(u*x+v*y) := by ring
   _ = _ := by rw [huv]; ring] at hi
 have hh := mul_le_mul_of_nonneg_left hi (show 0≤t^n/Real.sqrt t by positivity)
 convert hh using 1 <;> ring

theorem moving_integral_convex {n : ℕ} (hn : 2≤n) {a : ℝ} (ha : 0<a) :
 ConvexOn ℝ (Ioi 0) (fun z => ∫ t in 0..z, momentKernel n a z t) := by
 refine ⟨convex_Ioi 0, ?_⟩
 intro x hx y hy u v hu hv huv
 change 0<x at hx
 change 0<y at hy
 have hm : 0<u*x+v*y := (convex_Ioi (0:ℝ)) hx hy hu hv huv
 simp only [smul_eq_mul] at hm ⊢
 let L := max x (max y (u*x+v*y))
 have hLx : x≤L := le_max_left _ _
 have hLy : y≤L := (le_max_left _ _).trans (le_max_right _ _)
 have hLm : u*x+v*y≤L := (le_max_right _ _).trans (le_max_right _ _)
 have hn1 : 1≤n := by omega
 rw [moving_integral_truncated hn1 ha hm hLm,
  moving_integral_truncated hn1 ha hx hLx,
  moving_integral_truncated hn1 ha hy hLy]
 have hxI := (movingKernel_continuousOn (z := x) (L := L) hn1 ha).intervalIntegrable_of_Icc (μ := volume) (hx.le.trans hLx)
 have hyI := (movingKernel_continuousOn (z := y) (L := L) hn1 ha).intervalIntegrable_of_Icc (μ := volume) (hx.le.trans hLx)
 have hmI := (movingKernel_continuousOn (z := u*x+v*y) (L := L) hn1 ha).intervalIntegrable_of_Icc (μ := volume) (hx.le.trans hLx)
 rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
  ← intervalIntegral.integral_add (hxI.const_mul u) (hyI.const_mul v)]
 apply intervalIntegral.integral_mono_on (hx.le.trans hLx) hmI ((hxI.const_mul u).add (hyI.const_mul v))
 intro t _
 exact (movingKernel_convex hn a t).2 (mem_univ x) (mem_univ y) hu hv huv

theorem moment_convex (n : ℕ) {a : ℝ} (ha : 0<a) :
 ConvexOn ℝ (Ioi 0) (moment n a) := by
 rcases n with _ | n
 · exact moment_zero_convex ha
 rcases n with _ | n
 · exact moment_one_convex ha
 exact (fixed_integral_convex (n+2) ha).add (moving_integral_convex (by omega) ha)
end PendulumTimeMap
