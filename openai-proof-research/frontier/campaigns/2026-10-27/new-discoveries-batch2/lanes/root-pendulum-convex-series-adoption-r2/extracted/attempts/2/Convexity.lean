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
   simp [Real.zero_rpow (ne_of_gt hn'), show n≠0 by omega]
 · have ht' : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
   rw [Real.rpow_sub ht', Real.rpow_natCast, ← Real.sqrt_eq_rpow]
   ring

@[expose] def movingKernel (n : ℕ) (a z y : ℝ) : ℝ :=
 (max (z-y) 0)^((n:ℝ)-1/2) / Real.sqrt (a+y)

theorem movingKernel_convex {n : ℕ} (hn : 2≤n) {a y : ℝ} (ha : 0<a) (hy : 0≤y) :
 ConvexOn ℝ univ (fun z => movingKernel n a z y) := by
 have hp : (1:ℝ)≤(n:ℝ)-1/2 := by
  have : (2:ℝ)≤n := by exact_mod_cast hn
  linarith
 simpa only [movingKernel, div_eq_mul_inv, mul_comm] using
  (positivePart_rpow_convex hp y).smul (inv_nonneg.mpr (Real.sqrt_nonneg (a+y)))

theorem movingKernel_eq_zero {n : ℕ} (hn : 1≤n) {a z y : ℝ} (hy : z≤y) :
 movingKernel n a z y=0 := by
 have hp : (n:ℝ)-1/2≠0 := by
  have : (1:ℝ)≤n := by exact_mod_cast hn
  linarith
 simp [movingKernel, max_eq_right (sub_nonpos.mpr hy), Real.zero_rpow hp]

theorem movingKernel_eq_momentKernel {n : ℕ} (hn : 1≤n) {a z y : ℝ}
 (ha : 0<a) (hy : 0≤y) (hyz : y≤z) :
 movingKernel n a z y=momentKernel n a z (z-y) := by
 rw [momentKernel_rpow hn (sub_nonneg.mpr hyz) (by linarith)]
 unfold movingKernel
 rw [max_eq_left (sub_nonneg.mpr hyz)]
 congr 2 <;> ring

end PendulumTimeMap
