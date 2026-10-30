module
public import Moments
public import Source
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
  have : 0<u ∨ 0<v := by omega
  rcases this with h | h
  · nlinarith [mul_pos h hx, mul_nonneg hv hy.le]
  · nlinarith [mul_pos h hy, mul_nonneg hu hx.le]
 simp only [smul_eq_mul]
 rw [moment_zero ha hm, moment_zero ha hx, moment_zero ha hy]
 nlinarith

theorem moment_one_convex {a : ℝ} (ha : 0<a) :
 ConvexOn ℝ (Ioi 0) (moment 1 a) := by
 refine ⟨convex_Ioi 0, ?_⟩
 intro x hx y hy u v hu hv huv
 have hm : 0 < u*x+v*y := by
  have : 0<u ∨ 0<v := by omega
  rcases this with h | h
  · nlinarith [mul_pos h hx, mul_nonneg hv hy.le]
  · nlinarith [mul_pos h hy, mul_nonneg hu hx.le]
 have hs := Real.strictConcaveOn_sqrt.concaveOn.2
  (show a*x ∈ Ici 0 by exact (mul_pos ha hx).le)
  (show a*y ∈ Ici 0 by exact (mul_pos ha hy).le) hu hv huv
 simp only [smul_eq_mul] at hs ⊢
 rw [moment_one ha hm, moment_one ha hx, moment_one ha hy]
 rw [show a*(u*x+v*y)=u*(a*x)+v*(a*y) by ring]
 nlinarith

theorem positivePart_rpow_convex {p : ℝ} (hp : 1≤p) (y : ℝ) :
 ConvexOn ℝ univ (fun z : ℝ => (max (z-y) 0)^p) := by
 refine ⟨convex_univ, ?_⟩
 intro x _ z _ u v hu hv huv
 simp only [smul_eq_mul]
 have hmax : max (u*x+v*z-y) 0 ≤ u*max (x-y) 0+v*max (z-y) 0 := by
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left (le_max_left (x-y) 0) hu,
      mul_le_mul_of_nonneg_left (le_max_left (z-y) 0) hv]
  · positivity
 have hpow := Real.rpow_le_rpow (le_max_right (u*x+v*z-y) 0) hmax (by linarith : 0≤p)
 exact hpow.trans ((convexOn_rpow hp).2
  (show max (x-y) 0 ∈ Ici 0 from le_max_right _ _)
  (show max (z-y) 0 ∈ Ici 0 from le_max_right _ _) hu hv huv)

end PendulumTimeMap
