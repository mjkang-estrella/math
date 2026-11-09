import Mathlib

open Set Real

namespace FractionalBinomial

/-- Convex extrapolation from the exact anchors 1 and 2. -/
theorem convex_extrapolation {g : ℝ → ℝ} (hg : ConvexOn ℝ (Ioi 0) g)
    (h1 : g 1=0) (h2 : -Real.log 2 ≤ g 2) {a : ℝ} (ha : 2 ≤ a) :
    (1-a)*Real.log 2 ≤ g a := by
  have ha1 : 0<a-1 := by linarith
  have hw1 : 0 ≤ (a-2)/(a-1) := div_nonneg (by linarith) ha1.le
  have hw2 : 0 ≤ 1/(a-1) := by positivity
  have hsum : (a-2)/(a-1)+1/(a-1)=1 := by field_simp; ring
  have hpoint : ((a-2)/(a-1))*1+(1/(a-1))*a=2 := by field_simp; ring
  have h := hg.2 (show (1:ℝ)∈Ioi 0 by norm_num) (show a∈Ioi 0 by change 0<a; linarith)
    hw1 hw2 hsum
  simp only [smul_eq_mul, hpoint, h1, mul_zero, zero_add] at h
  have hmul := (mul_le_mul_of_nonneg_left (h2.trans h) ha1.le)
  have heq : (a-1)*((1/(a-1))*g a)=g a := by field_simp
  rw [heq] at hmul
  nlinarith

/-- Conditional reduction to log-convexity; this is not the source theorem by itself. -/
theorem bound_of_log_convex {F : ℝ → ℝ}
    (hlog : ConvexOn ℝ (Ioi 0) (fun a => Real.log (F a)))
    (h1 : F 1=1) (h2 : (1:ℝ)/2 ≤ F 2) {a : ℝ} (ha : 2 ≤ a) (hpos : 0<F a) :
    1 ≤ (2:ℝ)^(a-1)*F a := by
  have h2pos : 0<F 2 := by linarith
  have hlog2 : -Real.log 2 ≤ Real.log (F 2) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<1/2) h2
    simpa using h
  have hbound := convex_extrapolation hlog (by simp [h1]) hlog2 ha
  have hnon : 0 ≤ (a-1)*Real.log 2+Real.log (F a) := by linarith
  have hexp := Real.exp_le_exp.mpr hnon
  simpa only [Real.exp_zero, Real.exp_add, Real.exp_log hpos,
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2), mul_comm (Real.log 2) (a-1)] using hexp

/-- A finite sum of exponentials of convex functions has convex logarithm. -/
theorem convex_log_sum_exp {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {D : Set ℝ} (hD : Convex ℝ D) (f : ι → ℝ → ℝ)
    (hf : ∀ i∈s, ConvexOn ℝ D (f i)) :
    ConvexOn ℝ D (fun x => Real.log (∑ i∈s, Real.exp (f i x))) := by
  classical
  refine ⟨hD, ?_⟩
  intro x hx y hy a b ha hb hab
  let A := ∑ i∈s, Real.exp (f i x)
  let B := ∑ i∈s, Real.exp (f i y)
  have hA : 0<A := Finset.sum_pos (fun i _ => Real.exp_pos (f i x)) hs
  have hB : 0<B := Finset.sum_pos (fun i _ => Real.exp_pos (f i y)) hs
  have hz : 0<∑ i∈s, Real.exp (f i (a*x+b*y)) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) hs
  let M := Real.exp (a*Real.log A+b*Real.log B)
  have hi : ∀ i∈s, Real.exp (f i (a*x+b*y)) ≤
      M*(a*(Real.exp (f i x)/A)+b*(Real.exp (f i y)/B)) := by
    intro i his
    have hconv := (hf i his).2 hx hy ha hb hab
    simp only [smul_eq_mul] at hconv
    have hYoung := convexOn_exp.2 (mem_univ (f i x-Real.log A))
      (mem_univ (f i y-Real.log B)) ha hb hab
    simp only [smul_eq_mul] at hYoung
    have hY : Real.exp (a*(f i x-Real.log A)+b*(f i y-Real.log B)) ≤
        a*(Real.exp (f i x)/A)+b*(Real.exp (f i y)/B) := by
      simpa only [Real.exp_sub, Real.exp_log hA, Real.exp_log hB] using hYoung
    calc
      Real.exp (f i (a*x+b*y)) ≤ Real.exp (a*f i x+b*f i y) := Real.exp_le_exp.mpr hconv
      _ = M*Real.exp (a*(f i x-Real.log A)+b*(f i y-Real.log B)) := by
        dsimp [M]
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ M*(a*(Real.exp (f i x)/A)+b*(Real.exp (f i y)/B)) :=
        mul_le_mul_of_nonneg_left hY (Real.exp_pos _).le
  have hsum := Finset.sum_le_sum hi
  have hidentity : (∑ i∈s, M*(a*(Real.exp (f i x)/A)+b*(Real.exp (f i y)/B)))=M := by
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div]
    change M*(a*(A/A)+b*(B/B))=M
    rw [div_self hA.ne', div_self hB.ne', mul_one, mul_one, hab, mul_one]
  rw [hidentity] at hsum
  have hlog := Real.log_le_log hz hsum
  dsimp [M] at hlog
  rw [Real.log_exp] at hlog
  simpa only [smul_eq_mul] using hlog

end FractionalBinomial
