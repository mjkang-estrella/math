import GammaAssembly
import SeriesDefect

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open Set

namespace GammaLevel

/-- The analytic series is the genuine log-Gamma defect on its positive domain. -/
theorem seriesDefect_eq_logDefect {x s : ℝ} (hx : 0 < x) (hs : x < s) :
    seriesDefect x s = logDefect x s :=
  (gammaHasSum hx hs).tsum_eq

/-- Strict decrease in the literal Gamma defect, with no analytic premise. -/
theorem logDefect_strictAnti (x : ℝ) (hx : 0 < x) :
    StrictAntiOn (logDefect x) (Ioi x) := by
  intro s₀ hs₀ s₁ hs₁ hlt
  rw [← seriesDefect_eq_logDefect hx hs₁, ← seriesDefect_eq_logDefect hx hs₀]
  exact strictAnti_seriesDefect x hx hs₀ hs₁ hlt

/-- Existence and uniqueness for the actual source Gamma-ratio equation. -/
theorem existsUnique_sourceLevel {c x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    ∃! y : ℝ, SourceLevel c x y := by
  have hc0 : 0 < c := by linarith
  obtain ⟨y, ⟨hy, hval⟩, huniq⟩ :=
    existsUnique_seriesDefect x hx (Real.log_pos hc)
  have hbridge (z : ℝ) (hz : 0 < z) :
      seriesDefect x (x + z) = logDefect x (x + z) :=
    seriesDefect_eq_logDefect hx (by linarith)
  refine ⟨y, (sourceLevel_iff_defect hx hc0).mpr ⟨hy, ?_⟩, ?_⟩
  · rwa [← hbridge y hy]
  · intro z hz
    obtain ⟨hz0, hzval⟩ := (sourceLevel_iff_defect hx hc0).mp hz
    apply huniq z
    exact ⟨hz0, by rwa [hbridge z hz0]⟩

/-- Full literal source question, strengthened uniformly to every level c > 1. -/
theorem source_convexity : SourceConvexity := by
  intro c hc
  classical
  have hex : ∀ x : ℝ, ∃ y : ℝ, 0 < x → SourceLevel c x y := by
    intro x
    by_cases hx : 0 < x
    · obtain ⟨y, hy, _⟩ := existsUnique_sourceLevel hc hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun hx' => False.elim (hx hx')⟩
  choose h hh using hex
  refine ⟨h, hh, ?_⟩
  exact literal_height_strictConvexOn_of_strictAnti
    logDefect_strictAnti (by linarith) hh

/-- Published Remark 16(a), the source's level 2 instance on all x > 0. -/
theorem source_remark16a : ∃ h : ℝ → ℝ,
    (∀ x : ℝ, 0 < x → SourceLevel 2 x (h x)) ∧
    StrictConvexOn ℝ (Ioi 0) h :=
  source_convexity 2 (by norm_num)

end GammaLevel
