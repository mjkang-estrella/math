import StrictJensen

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open Set Filter Topology
namespace GammaLevel

theorem defect_strict_mixture
    (hseries : ∀ x s : ℝ, 0 < x → x < s →
      HasSum (seriesTerm x s) (logDefect x s))
    {a b x₀ x₁ s₀ s₁ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx₀ : 0 < x₀) (hx₁ : 0 < x₁) (hs₀ : x₀ < s₀) (hs₁ : x₁ < s₁)
    (hne : x₀ ≠ x₁) :
    logDefect (a * x₀ + b * x₁) (a * s₀ + b * s₁) <
      (a * x₀ / (a * x₀ + b * x₁)) * logDefect x₀ s₀ +
      (b * x₁ / (a * x₀ + b * x₁)) * logDefect x₁ s₁ := by
  have hX : 0 < a * x₀ + b * x₁ := add_pos (mul_pos ha hx₀) (mul_pos hb hx₁)
  have hS : a * x₀ + b * x₁ < a * s₀ + b * s₁ :=
    add_lt_add (mul_lt_mul_of_pos_left hs₀ ha) (mul_lt_mul_of_pos_left hs₁ hb)
  have h₀ := hseries x₀ s₀ hx₀ hs₀
  have h₁ := hseries x₁ s₁ hx₁ hs₁
  have hM := hseries _ _ hX hS
  have h := strict_tsum_mixture ha hb hab hx₀ hx₁ hs₀ hs₁ hne
    h₀.summable h₁.summable hM.summable
  rwa [h₀.tsum_eq, h₁.tsum_eq, hM.tsum_eq] at h

theorem level_height_strictConvexOn
    (hseries : ∀ x s : ℝ, 0 < x → x < s →
      HasSum (seriesTerm x s) (logDefect x s))
    (hanti : ∀ x : ℝ, 0 < x → StrictAntiOn (logDefect x) (Ioi x))
    {h : ℝ → ℝ} {d : ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < h x)
    (hlevel : ∀ x : ℝ, 0 < x → logDefect x (x + h x) = d) :
    StrictConvexOn ℝ (Ioi 0) h := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x₀ hx₀ x₁ hx₁ hne a b ha hb hab
  change 0 < x₀ at hx₀
  change 0 < x₁ at hx₁
  have hX : 0 < a * x₀ + b * x₁ := add_pos (mul_pos ha hx₀) (mul_pos hb hx₁)
  have hp₀ := hpos x₀ hx₀
  have hp₁ := hpos x₁ hx₁
  have hY : 0 < a * h x₀ + b * h x₁ := add_pos (mul_pos ha hp₀) (mul_pos hb hp₁)
  have hM := defect_strict_mixture hseries ha hb hab hx₀ hx₁
    (by linarith : x₀ < x₀ + h x₀) (by linarith : x₁ < x₁ + h x₁) hne
  rw [hlevel x₀ hx₀, hlevel x₁ hx₁] at hM
  obtain ⟨_, _, hw⟩ := mixed_weights ha hb hx₀ hx₁
  have hR : a * x₀ / (a * x₀ + b * x₁) * d +
      b * x₁ / (a * x₀ + b * x₁) * d = d := by
    nlinarith [congrArg (fun t : ℝ => t * d) hw]
  rw [hR] at hM
  have hfinal : h (a * x₀ + b * x₁) < a * h x₀ + b * h x₁ := by
    by_contra hn
    have hn' : a * h x₀ + b * h x₁ ≤ h (a * x₀ + b * x₁) := le_of_not_gt hn
    have he : a * (x₀ + h x₀) + b * (x₁ + h x₁) ≤
        a * x₀ + b * x₁ + h (a * x₀ + b * x₁) := by nlinarith
    have hd := (hanti _ hX).antitoneOn
      (show a * (x₀ + h x₀) + b * (x₁ + h x₁) ∈ Ioi (a * x₀ + b * x₁) by
        change a * x₀ + b * x₁ < a * (x₀ + h x₀) + b * (x₁ + h x₁)
        nlinarith)
      (show a * x₀ + b * x₁ + h (a * x₀ + b * x₁) ∈ Ioi (a * x₀ + b * x₁) by
        change a * x₀ + b * x₁ < a * x₀ + b * x₁ + h (a * x₀ + b * x₁)
        linarith [hpos _ hX]) he
    rw [hlevel _ hX] at hd
    linarith
  simpa only [smul_eq_mul] using hfinal

end GammaLevel
