import BinomialConverse

open Set Real

namespace FractionalBinomial

lemma convex_anchor_extrapolation {g : ℝ → ℝ} (hg : ConvexOn ℝ (Ioi 0) g)
    (h1 : g 1=0) {a : ℝ} (ha : 2 ≤ a) : (a-1)*g 2 ≤ g a := by
  have ha1 : 0<a-1 := by linarith
  have hw1 : 0 ≤ (a-2)/(a-1) := div_nonneg (by linarith) ha1.le
  have hw2 : 0 ≤ 1/(a-1) := by positivity
  have hsum : (a-2)/(a-1)+1/(a-1)=1 := by field_simp; ring
  have hpoint : ((a-2)/(a-1))*1+(1/(a-1))*a=2 := by field_simp; ring
  have h := hg.2 (show (1:ℝ)∈Ioi 0 by norm_num)
    (show a∈Ioi 0 by change 0<a; linarith) hw1 hw2 hsum
  simp only [smul_eq_mul, hpoint, h1, mul_zero, zero_add] at h
  have hm := mul_le_mul_of_nonneg_left h ha1.le
  have heq : (a-1)*((1/(a-1))*g a)=g a := by field_simp
  rwa [heq] at hm

theorem normalized_biased_bound_positive (k : ℕ) {a p q : ℝ} (ha : 2 ≤ a)
    (hp : 0<p) (hq : 0<q) (hs : p+q=1) :
    (((1+(-p+q)^(2*k))/2):ℝ)^(a-1) ≤ binomialSum k a p q := by
  have hg := binomialSum_log_convex_of_grid gridMajorizes_proved k hp hq
  have h1 : Real.log (binomialSum k 1 p q)=0 := by rw [binomialSum_one, hs]; simp
  have h := convex_anchor_extrapolation hg h1 ha
  have hpos2 := binomialSum_pos k (by norm_num : (0:ℝ)<2) hp hq
  have hposa := binomialSum_pos k (by linarith : 0<a) hp hq
  have he := Real.exp_le_exp.mpr h
  rw [Real.exp_log hposa] at he
  have heq : binomialSum k 2 p q=(1+(-p+q)^(2*k))/2 := by
    have ht := binomialSum_two k p q
    rw [hs, one_pow] at ht
    linarith
  have hr : (binomialSum k 2 p q)^(a-1) ≤ binomialSum k a p q := by
    simpa only [Real.rpow_def_of_pos hpos2, mul_comm] using he
  rwa [heq] at hr

theorem normalized_biased_bound (k : ℕ) {a p q : ℝ} (ha : 2 ≤ a)
    (hp : 0≤p) (hq : 0≤q) (hs : p+q=1) :
    (((1+(-p+q)^(2*k))/2):ℝ)^(a-1) ≤ binomialSum k a p q := by
  by_cases hp0 : p=0
  · have hq1 : q=1 := by linarith
    subst p; subst q
    simpa using binomialSum_endpoint_left k (by linarith : 0<a)
      (le_refl (0:ℝ)) (by norm_num : (0:ℝ)≤1)
  by_cases hq0 : q=0
  · have hp1 : p=1 := by linarith
    subst p; subst q
    have hn : (-1:ℝ)^(2*k)=1 := by rw [pow_mul]; simp
    simpa [hn] using binomialSum_endpoint_right k (by linarith : 0<a)
      (by norm_num : (0:ℝ)≤1) (le_refl (0:ℝ))
  exact normalized_biased_bound_positive k ha (lt_of_le_of_ne hp (Ne.symm hp0))
    (lt_of_le_of_ne hq (Ne.symm hq0)) hs

theorem homogeneous_biased_bound (k : ℕ) {a x y : ℝ} (ha : 2≤a)
    (hx : 0≤x) (hy : 0≤y) (hc : 0<x+y) :
    (x+y)^(a*k)*(((1+(-x/(x+y)+y/(x+y))^(2*k))/2):ℝ)^(a-1)
      ≤ binomialSum k a x y := by
  have hp := div_nonneg hx hc.le
  have hq := div_nonneg hy hc.le
  have hs : x/(x+y)+y/(x+y)=1 := by field_simp
  have h := normalized_biased_bound k ha hp hq hs
  have hh := binomialSum_scale k a hp hq hc
  rw [mul_div_cancel₀ x hc.ne', mul_div_cancel₀ y hc.ne'] at hh
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_pos_of_pos hc (a*k)).le
  rw [← hh] at hm
  simpa only [neg_div] using hm

lemma binomialSum_degree_one {a : ℝ} (ha : 0<a) (x y : ℝ) :
    binomialSum 1 a x y=x^a+y^a := by
  simp [binomialSum, Finset.sum_range_succ, generalizedBinomial_zero 1 ha,
    generalizedBinomial_self 1 ha, add_comm]

theorem sharp_coefficient {a C : ℝ} (ha : 2≤a)
    (hC : ∀ (k : ℕ) (x y : ℝ), 0≤x → 0≤y →
      (x+y)^(a*k) ≤ C*binomialSum k a x y) : (2:ℝ)^(a-1) ≤ C := by
  have h := hC 1 1 1 (by norm_num) (by norm_num)
  rw [binomialSum_degree_one (by linarith : 0<a)] at h
  simp only [one_add_one_eq_two, Nat.cast_one, mul_one, Real.one_rpow] at h
  have heq : (2:ℝ)^a=(2:ℝ)^(a-1)*2 := by
    calc
      (2:ℝ)^a = (2:ℝ)^((a-1)+1) := by congr 1; ring
      _ = (2:ℝ)^(a-1)*(2:ℝ)^(1:ℝ) := Real.rpow_add (by norm_num) _ _
      _ = _ := by rw [Real.rpow_one]
  rw [heq] at h
  linarith

end FractionalBinomial
