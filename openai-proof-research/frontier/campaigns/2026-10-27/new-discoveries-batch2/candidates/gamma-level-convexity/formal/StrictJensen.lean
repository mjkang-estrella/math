import ProfileConvex

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open Set Filter Topology
namespace GammaLevel

theorem mixed_ratio_identity {a b x₀ x₁ s₀ s₁ : ℝ}
    (hx₀ : 0 < x₀) (hx₁ : 0 < x₁) (hab : a + b = 1) (m : ℕ) :
    (a * s₀ + b * s₁ + m) / (a * x₀ + b * x₁) =
      (a * x₀ / (a * x₀ + b * x₁)) * ((s₀ + m) / x₀) +
      (b * x₁ / (a * x₀ + b * x₁)) * ((s₁ + m) / x₁) := by
  calc
    _ = (a * (s₀ + m) + b * (s₁ + m)) / (a * x₀ + b * x₁) := by
      congr 1
      nlinarith [congrArg (fun t : ℝ => t * (m : ℝ)) hab]
    _ = _ := by
      field_simp

theorem distinct_shift_ratios {x₀ x₁ s₀ s₁ : ℝ}
    (hx₀ : 0 < x₀) (hx₁ : 0 < x₁) (hne : x₀ ≠ x₁) :
    ∃ m : ℕ, (s₀ + m) / x₀ ≠ (s₁ + m) / x₁ := by
  by_cases h : s₀ / x₀ = s₁ / x₁
  · refine ⟨1, ?_⟩
    intro h₁
    norm_num at h₁
    have e₀ := (div_eq_div_iff hx₀.ne' hx₁.ne').mp h
    have e₁ := (div_eq_div_iff hx₀.ne' hx₁.ne').mp h₁
    apply hne
    nlinarith
  · exact ⟨0, by simpa using h⟩

theorem mixed_weights {a b x₀ x₁ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx₀ : 0 < x₀) (hx₁ : 0 < x₁) :
    0 < a * x₀ / (a * x₀ + b * x₁) ∧
      0 < b * x₁ / (a * x₀ + b * x₁) ∧
      a * x₀ / (a * x₀ + b * x₁) + b * x₁ / (a * x₀ + b * x₁) = 1 := by
  have hX : 0 < a * x₀ + b * x₁ := add_pos (mul_pos ha hx₀) (mul_pos hb hx₁)
  refine ⟨div_pos (mul_pos ha hx₀) hX, div_pos (mul_pos hb hx₁) hX, ?_⟩
  rw [← add_div, div_self hX.ne']

theorem mixed_term_le {a b x₀ x₁ s₀ s₁ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx₀ : 0 < x₀) (hx₁ : 0 < x₁) (hs₀ : x₀ < s₀) (hs₁ : x₁ < s₁)
    (m : ℕ) :
    seriesTerm (a * x₀ + b * x₁) (a * s₀ + b * s₁) m ≤
      (a * x₀ / (a * x₀ + b * x₁)) * seriesTerm x₀ s₀ m +
      (b * x₁ / (a * x₀ + b * x₁)) * seriesTerm x₁ s₁ m := by
  have h₀ : (s₀ + m) / x₀ ∈ Ioi (1 : ℝ) := by
    apply (lt_div_iff₀ hx₀).mpr
    nlinarith [(Nat.cast_nonneg m : 0 ≤ (m : ℝ))]
  have h₁ : (s₁ + m) / x₁ ∈ Ioi (1 : ℝ) := by
    apply (lt_div_iff₀ hx₁).mpr
    nlinarith [(Nat.cast_nonneg m : 0 ≤ (m : ℝ))]
  obtain ⟨hw₀, hw₁, hw⟩ := mixed_weights ha hb hx₀ hx₁
  have h := profile_strictConvexOn.convexOn.2 h₀ h₁ hw₀.le hw₁.le hw
  dsimp [seriesTerm]
  rw [mixed_ratio_identity hx₀ hx₁ hab m]
  simpa only [smul_eq_mul] using h

theorem mixed_term_lt {a b x₀ x₁ s₀ s₁ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx₀ : 0 < x₀) (hx₁ : 0 < x₁) (hs₀ : x₀ < s₀) (hs₁ : x₁ < s₁)
    (m : ℕ) (hne : (s₀ + m) / x₀ ≠ (s₁ + m) / x₁) :
    seriesTerm (a * x₀ + b * x₁) (a * s₀ + b * s₁) m <
      (a * x₀ / (a * x₀ + b * x₁)) * seriesTerm x₀ s₀ m +
      (b * x₁ / (a * x₀ + b * x₁)) * seriesTerm x₁ s₁ m := by
  have h₀ : (s₀ + m) / x₀ ∈ Ioi (1 : ℝ) := by
    apply (lt_div_iff₀ hx₀).mpr
    nlinarith [(Nat.cast_nonneg m : 0 ≤ (m : ℝ))]
  have h₁ : (s₁ + m) / x₁ ∈ Ioi (1 : ℝ) := by
    apply (lt_div_iff₀ hx₁).mpr
    nlinarith [(Nat.cast_nonneg m : 0 ≤ (m : ℝ))]
  obtain ⟨hw₀, hw₁, hw⟩ := mixed_weights ha hb hx₀ hx₁
  have h := profile_strictConvexOn.2 h₀ h₁ hne hw₀ hw₁ hw
  dsimp [seriesTerm]
  rw [mixed_ratio_identity hx₀ hx₁ hab m]
  simpa only [smul_eq_mul] using h

theorem strict_tsum_mixture {a b x₀ x₁ s₀ s₁ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx₀ : 0 < x₀) (hx₁ : 0 < x₁) (hs₀ : x₀ < s₀) (hs₁ : x₁ < s₁)
    (hne : x₀ ≠ x₁)
    (hsum₀ : Summable (seriesTerm x₀ s₀)) (hsum₁ : Summable (seriesTerm x₁ s₁))
    (hsumX : Summable (seriesTerm (a * x₀ + b * x₁) (a * s₀ + b * s₁))) :
    (∑' m, seriesTerm (a * x₀ + b * x₁) (a * s₀ + b * s₁) m) <
      (a * x₀ / (a * x₀ + b * x₁)) * (∑' m, seriesTerm x₀ s₀ m) +
      (b * x₁ / (a * x₀ + b * x₁)) * (∑' m, seriesTerm x₁ s₁ m) := by
  obtain ⟨m, hm⟩ := distinct_shift_ratios hx₀ hx₁ hne
  have hsum := (hsum₀.mul_left (a * x₀ / (a * x₀ + b * x₁))).add
    (hsum₁.mul_left (b * x₁ / (a * x₀ + b * x₁)))
  have h := hsumX.tsum_lt_tsum
    (mixed_term_le ha hb hab hx₀ hx₁ hs₀ hs₁)
    (mixed_term_lt ha hb hab hx₀ hx₁ hs₀ hs₁ m hm) hsum
  rw [(hsum₀.mul_left _).tsum_add (hsum₁.mul_left _), tsum_mul_left, tsum_mul_left] at h
  exact h

end GammaLevel
