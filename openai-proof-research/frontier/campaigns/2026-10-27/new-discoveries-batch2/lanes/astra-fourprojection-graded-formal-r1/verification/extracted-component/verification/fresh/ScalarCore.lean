import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace FourProjection

lemma denominator_pos (a b : ℝ) (ha : a ^ 2 < 1) (hb : b ^ 2 < 1) :
    0 < 1 + a * b := by
  nlinarith [sq_nonneg (a + b)]

lemma sqrt_lower (a b : ℝ) (ha : a ^ 2 < 1) (hb : b ^ 2 < 1) :
    (1 - (a ^ 2 + b ^ 2)) * (1 + a * b) ≤
      Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) := by
  have hd := denominator_pos a b ha hb
  have hr : 0 ≤ (1 - a ^ 2) * (1 - b ^ 2) := mul_nonneg (by linarith) (by linarith)
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg ((1 - a ^ 2) * (1 - b ^ 2))
  by_cases ht : 1 ≤ a ^ 2 + b ^ 2
  · have hh : (1 - (a ^ 2 + b ^ 2)) * (1 + a * b) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hd)
    linarith
  · have ht' : 0 ≤ 1 - (a ^ 2 + b ^ 2) := by linarith
    by_cases hab : 0 ≤ a * b
    · have hy : 0 ≤ 1 - (a ^ 2 + b ^ 2) + a * b := by linarith
      have hi : (1 - a ^ 2) * (1 - b ^ 2) -
          (1 - (a ^ 2 + b ^ 2) + a * b) ^ 2 =
          (a - b) ^ 2 * (1 - (a ^ 2 + b ^ 2)) := by ring
      have hp := mul_nonneg (sq_nonneg (a - b)) ht'
      have hl : 1 - (a ^ 2 + b ^ 2) + a * b ≤
          Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) := by nlinarith
      have hp' := mul_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b)) hab
      nlinarith
    · have hi : (1 - a ^ 2) * (1 - b ^ 2) - (1 - (a ^ 2 + b ^ 2)) ^ 2 =
          (a ^ 2 + b ^ 2) * (1 - (a ^ 2 + b ^ 2)) + (a * b) ^ 2 := by ring
      have hp := mul_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b)) ht'
      have hl : 1 - (a ^ 2 + b ^ 2) ≤
          Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) := by nlinarith [sq_nonneg (a * b)]
      have hp' := mul_nonpos_of_nonneg_of_nonpos ht' (le_of_not_ge hab)
      nlinarith

 theorem scalar_coefficient (a b : ℝ) (ha : a ^ 2 < 1) (hb : b ^ 2 < 1) :
    1 - Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) / (1 + a * b) ≤ a ^ 2 + b ^ 2 := by
  have h := (le_div_iff₀ (denominator_pos a b ha hb)).2 (sqrt_lower a b ha hb)
  linarith

lemma weight_inequality (a b u v : ℝ) (ha : a ^ 2 < 1) (hb : b ^ 2 < 1)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hu : u ^ 2 = (1+a)*(1+b))
    (hv : v ^ 2 = (1-a)*(1-b)) :
    (u-v)^2 ≤ (a^2+b^2)*(u^2+v^2) := by
  have hr : 0 ≤ (1-a^2)*(1-b^2) := mul_nonneg (by linarith) (by linarith)
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg ((1-a^2)*(1-b^2))
  have hp := mul_nonneg hu0 hv0
  have he : (u*v)^2 = (1-a^2)*(1-b^2) := by
    calc
      (u*v)^2 = u^2*v^2 := by ring
      _ = ((1+a)*(1+b))*((1-a)*(1-b)) := by rw [hu,hv]
      _ = _ := by ring
  have huv : u*v = Real.sqrt ((1-a^2)*(1-b^2)) := by nlinarith
  have hd : u^2+v^2 = 2*(1+a*b) := by nlinarith [hu,hv]
  have hl := sqrt_lower a b ha hb
  rw [← huv] at hl
  nlinarith [hd]

lemma real_pair (a b u v x y : ℝ) (ha : a ^ 2 < 1) (hb : b ^ 2 < 1)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hu : u ^ 2 = (1+a)*(1+b))
    (hv : v ^ 2 = (1-a)*(1-b)) (hrel : u*x+v*y=0) :
    (x+y)^2 ≤ (a^2+b^2)*(x^2+y^2) := by
  have hc := weight_inequality a b u v ha hb hu0 hv0 hu hv
  have hd : 0 < u^2+v^2 := by
    have hp := denominator_pos a b ha hb
    nlinarith [hu,hv]
  have hi : (u^2+v^2)*(x+y)^2 - (u-v)^2*(x^2+y^2) = 0 := by
    calc
      _ = 2*(u*x+v*y)*(v*x+u*y) := by ring
      _ = 0 := by rw [hrel]; ring
  have hm := mul_le_mul_of_nonneg_right hc (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have hh : (u^2+v^2)*(x+y)^2 ≤ (u^2+v^2)*((a^2+b^2)*(x^2+y^2)) := by
    nlinarith [hi]
  exact (mul_le_mul_iff_right₀ hd).mp hh

 theorem complex_pair (a b u v : ℝ) (x y : ℂ)
    (ha : a ^ 2 < 1) (hb : b ^ 2 < 1)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hu : u ^ 2 = (1+a)*(1+b))
    (hv : v ^ 2 = (1-a)*(1-b)) (hrel : (u:ℂ)*x+(v:ℂ)*y=0) :
    Complex.normSq (x+y) ≤ (a^2+b^2)*(Complex.normSq x+Complex.normSq y) := by
  have hreal : u*x.re+v*y.re=0 := by
    have h := congrArg Complex.re hrel
    simpa using h
  have himag : u*x.im+v*y.im=0 := by
    have h := congrArg Complex.im hrel
    simpa using h
  have hr := real_pair a b u v x.re y.re ha hb hu0 hv0 hu hv hreal
  have hi := real_pair a b u v x.im y.im ha hb hu0 hv0 hu hv himag
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith

#print axioms denominator_pos
#print axioms sqrt_lower
#print axioms scalar_coefficient
#print axioms weight_inequality
#print axioms real_pair
#print axioms complex_pair
end FourProjection
