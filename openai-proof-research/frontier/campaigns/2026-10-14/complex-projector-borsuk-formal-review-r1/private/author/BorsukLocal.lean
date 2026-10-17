import Mathlib

/- Copyright 2026 Myeongjin Kang. MIT.
Scoped support for B8C Lemma 11. This file does not formalize CP² or Borsuk–Ulam. -/

namespace BorsukLocal

noncomputable def favored (a b ε : ℝ) : ℝ := a - b^2 + (2/5 : ℝ)*ε - 2*ε^2
noncomputable def other (a b ε : ℝ) : ℝ := b - a^2 - (13/4 : ℝ)*ε - 2*ε^2
noncomputable def radius : ℝ := 1 / (12 * Real.sqrt 3)

/-- The favored trio wins in the region b² ≤ a, including equality. -/
theorem favored_case {a b ε : ℝ} (hε : 0 < ε) (hεmax : ε ≤ 1/50)
    (hcase : b^2 ≤ a) : (9/25 : ℝ)*ε ≤ favored a b ε := by
  unfold favored
  nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hεmax)]

/-- In the second region the transverse square is at most b/1000. -/
theorem transverse_square {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbsmall : b ≤ 1/10) (hcase : a < b^2) : a^2 < b/1000 := by
  have hab : a^2 < (b^2)^2 := by
    nlinarith [mul_pos (sub_pos.mpr hcase) (show 0 < b^2+a by nlinarith)]
  have hb3 : b^3 ≤ (1/10 : ℝ)^3 := by gcongr
  have hb4 : b^4 ≤ b/1000 := by
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hb3)]
  nlinarith

/-- The other trio wins for b² > a and b ≥ 4ε, including b = 4ε. -/
theorem other_large_case {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbsmall : b ≤ 1/10) (hε : 0 < ε) (hεmax : ε ≤ 1/50)
    (hcase : a < b^2) (hlarge : 4*ε ≤ b) :
    (353/500 : ℝ)*ε < other a b ε := by
  have hsq := transverse_square ha hb hbsmall hcase
  unfold other
  nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hεmax)]

/-- The favored trio wins when b < 4ε; this estimate needs no b² > a. -/
theorem favored_small_case {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hεmax : ε ≤ 1/50) (hsmall : b < 4*ε) :
    ε/25 < favored a b ε := by
  have hsq : b^2 < 16*ε^2 := by
    nlinarith [mul_pos (sub_pos.mpr hsmall) (show 0 < 4*ε+b by linarith)]
  unfold favored
  nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hεmax)]

/-- Exhaustive three-case result; both nonnegative chart magnitudes are explicit. -/
theorem two_trio_margin {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbsmall : b ≤ 1/10) (hε : 0 < ε) (hεmax : ε ≤ 1/50) :
    ε/25 < max (favored a b ε) (other a b ε) := by
  by_cases hcase : b^2 ≤ a
  · have hf := favored_case hε hεmax hcase
    have hm := le_max_left (favored a b ε) (other a b ε)
    linarith
  · have hcase' : a < b^2 := lt_of_not_ge hcase
    by_cases hlarge : 4*ε ≤ b
    · have ho := other_large_case ha hb hbsmall hε hεmax hcase' hlarge
      have hm := le_max_right (favored a b ε) (other a b ε)
      linarith
    · have hf := favored_small_case ha hb hε hεmax (lt_of_not_ge hlarge)
      exact lt_of_lt_of_le hf (le_max_left _ _)

/-- Exact lower rational bound for the favored radical coefficient. -/
theorem favored_radical_lower : (2/5 : ℝ) < 1 / Real.sqrt 6 := by
  have hs : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  apply (lt_div_iff₀ hs).2
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)]

/-- Exact upper rational bound for the other trio's radical coefficient. -/
theorem other_radical_upper : 2 * Real.sqrt 2 + 1 / Real.sqrt 6 < (13/4 : ℝ) := by
  have h2 : Real.sqrt 2 < (99/70 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ)]
  have hs : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have h6 : 1 / Real.sqrt 6 < (41/100 : ℝ) := by
    apply (div_lt_iff₀ hs).2
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)]
  linarith

/-- The published radius has exactly the stated rational squared value. -/
theorem radius_sq : radius^2 = (1/432 : ℝ) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  unfold radius
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

/-- Small-chart bounds are proved, not postulated as decimal approximations. -/
theorem radius_bounds : 0 < radius ∧ radius < (1/20 : ℝ) ∧ radius^3 < (1/1000 : ℝ) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hr : 0 < radius := by unfold radius; positivity
  have hr20 : radius < (1/20 : ℝ) := by
    unfold radius
    apply (div_lt_iff₀ (by positivity : 0 < 12 * Real.sqrt 3)).2
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hr3 : radius^3 < (1/10 : ℝ)^3 := by gcongr; linarith
  exact ⟨hr, hr20, by norm_num at hr3 ⊢; exact hr3⟩

/-- The full chart bound gives all numerical hypotheses and N² < 2. -/
theorem chart_bounds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hchart : a^2+b^2 < radius^2) :
    a < 1/20 ∧ b < 1/20 ∧ 1+a^2+b^2 < 2 := by
  rw [radius_sq] at hchart
  constructor
  · nlinarith [sq_nonneg b]
  constructor
  · nlinarith [sq_nonneg a]
  · linarith

/-- The actual radical lower estimates imply positivity of one scaled score. -/
theorem two_trio_scaled_positive {a b ε E₁ E₂ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hchart : a^2+b^2 < radius^2) (hε : 0 < ε) (hεmax : ε ≤ 1/50)
    (hF : a-b^2+ε/Real.sqrt 6-2*ε^2 < E₁)
    (hO : b-a^2-(2*Real.sqrt 2+1/Real.sqrt 6)*ε-2*ε^2 ≤ E₂) :
    0 < E₁ ∨ 0 < E₂ := by
  have hc := chart_bounds ha hb hchart
  have hm := two_trio_margin ha hb (by linarith : b ≤ 1/10) hε hεmax
  have hf : favored a b ε < E₁ := by
    unfold favored
    have hh : (2/5 : ℝ)*ε < ε/Real.sqrt 6 := by
      convert mul_lt_mul_of_pos_right favored_radical_lower hε using 1; ring
    linarith
  have ho : other a b ε ≤ E₂ := by
    unfold other
    have hh := mul_pos (sub_pos.mpr other_radical_upper) hε
    nlinarith
  rcases lt_max_iff.mp hm with hh | hh
  · left; linarith
  · right; linarith

/-- This links the scaled polynomial conclusion to the score threshold 1/2. -/
theorem local_score_improves {a b ε x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hchart : a^2+b^2 < radius^2) (hε : 0 < ε) (hεmax : ε ≤ 1/50)
    (hF : a-b^2+ε/Real.sqrt 6-2*ε^2 < 2*(1+a^2+b^2)*(1+ε^2)*(x-1/2))
    (hO : b-a^2-(2*Real.sqrt 2+1/Real.sqrt 6)*ε-2*ε^2 ≤
      2*(1+a^2+b^2)*(1+ε^2)*(y-1/2)) : 1/2 < x ∨ 1/2 < y := by
  have hp : 0 < 2*(1+a^2+b^2)*(1+ε^2) := by positivity
  rcases two_trio_scaled_positive ha hb hchart hε hεmax hF hO with hx | hy
  · have hh := (mul_pos_iff_of_pos_left hp).mp hx
    exact Or.inl (by linarith)
  · have hh := (mul_pos_iff_of_pos_left hp).mp hy
    exact Or.inr (by linarith)

/-- Numeric Bessel implication. Orthogonality-to-Bessel is a separate geometric input. -/
theorem bessel_cap_incompatible {x y δ : ℝ} (hδ : 0 < δ)
    (hx : 1/2+δ ≤ x) (hy : 1/2+δ ≤ y) : ¬ x+y ≤ 1 := by linarith

/-- Numeric far-region margin, including ε = η/3. -/
theorem complementary_margin {η ε M₀ Mε : ℝ} (hη : 0 < η) (hε : ε ≤ η/3)
    (hbase : 1/2+η ≤ M₀) (hchange : M₀-2*ε ≤ Mε) :
    1/2+η/3 ≤ Mε ∧ 1/2 < Mε := by constructor <;> linarith

/-- Complex score expansion after extracting the common 1/sqrt(2) factor.
Here q = gamma*z₂, so normSq q = |z₂|² when |gamma| = 1.
The conjugate is on (1+q), as in the frozen proof. -/
theorem score_numerator_expansion (q D : ℂ) (ε b : ℝ) :
    Complex.normSq (1+q+(Real.sqrt 2 * ε : ℝ)*D) -
      (1+ε^2)*(1+Complex.normSq q+b^2) =
    2*q.re-b^2 + 2*Real.sqrt 2*ε*((starRingEnd ℂ (1+q))*D).re +
      2*ε^2*Complex.normSq D - ε^2*(1+Complex.normSq q+b^2) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]
  ring_nf
  norm_num [Real.sq_sqrt]
  ring

/-- Division by the actual positive normalization preserves the score identity. -/
theorem score_scaled_expansion (q D : ℂ) (ε b : ℝ) :
    2*(1+Complex.normSq q+b^2)*(1+ε^2)*
      (Complex.normSq (1+q+(Real.sqrt 2 * ε : ℝ)*D) /
        (2*(1+Complex.normSq q+b^2)*(1+ε^2)) - 1/2) =
    2*q.re-b^2 + 2*Real.sqrt 2*ε*((starRingEnd ℂ (1+q))*D).re +
      2*ε^2*Complex.normSq D - ε^2*(1+Complex.normSq q+b^2) := by
  have hp : 0 < 2*(1+Complex.normSq q+b^2)*(1+ε^2) := by
    have hn := Complex.normSq_nonneg q
    positivity
  have hn : 1+Complex.normSq q+b^2 ≠ 0 := by
    have hh := Complex.normSq_nonneg q
    positivity
  rw [← score_numerator_expansion]
  field_simp [hn]

end BorsukLocal
