import ConvexAssembly
import GammaEuler
import GammaRatio

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open Set

namespace GammaLevel

/-- The actual Gamma defect satisfies the strict mixed-level inequality. -/
theorem gamma_defect_strict_mixture {a b x₀ x₁ s₀ s₁ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx₀ : 0 < x₀) (hx₁ : 0 < x₁) (hs₀ : x₀ < s₀) (hs₁ : x₁ < s₁)
    (hne : x₀ ≠ x₁) :
    logDefect (a * x₀ + b * x₁) (a * s₀ + b * s₁) <
      (a * x₀ / (a * x₀ + b * x₁)) * logDefect x₀ s₀ +
      (b * x₁ / (a * x₀ + b * x₁)) * logDefect x₁ s₁ :=
  defect_strict_mixture gammaHasSum' ha hb hab hx₀ hx₁ hs₀ hs₁ hne

/-- Remaining assembly premises are explicit: literal levels and strict decrease.
The Gamma-series identity is discharged by the closed Bohr--Mollerup bridge. -/
theorem literal_height_strictConvexOn_of_strictAnti
    (hanti : ∀ x : ℝ, 0 < x → StrictAntiOn (logDefect x) (Ioi x))
    {c : ℝ} (hc : 0 < c) {h : ℝ → ℝ}
    (hlevel : ∀ x : ℝ, 0 < x → SourceLevel c x (h x)) :
    StrictConvexOn ℝ (Ioi 0) h := by
  apply level_height_strictConvexOn gammaHasSum' hanti
  · intro x hx
    exact (hlevel x hx).1
  · intro x hx
    exact ((sourceLevel_iff_defect hx hc).mp (hlevel x hx)).2

end GammaLevel
