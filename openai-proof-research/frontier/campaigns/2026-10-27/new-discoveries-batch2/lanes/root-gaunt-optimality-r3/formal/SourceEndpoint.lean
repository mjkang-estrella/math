import WeightedComparison

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
noncomputable section

namespace GauntIntegral

def sourceOrder (n v : ℝ) : ℝ := Real.sqrt ((v + n) ^ 2 - 2 * v - 1)

def SourceClaim339406Lower : Prop := ∀ n v : ℝ, n < 1 →
  1 - n + Real.sqrt (2 * (1 - n)) ≤ v → ∀ x : ℝ, 0 < x →
    x ^ (-v) * besselK (sourceOrder n v) x <
      ∫ t in Ioi x, t ^ (-v) * besselK (v + n) t

theorem source_parameter_geometry {n v : ℝ} (hn : n < 1)
    (hv : 1 - n + Real.sqrt (2 * (1 - n)) ≤ v) :
    0 ≤ sourceOrder n v ∧ sourceOrder n v < v ∧
      (v + n) ^ 2 = (sourceOrder n v) ^ 2 + 2 * v + 1 := by
  have hp : 0 < 1 - n := by linarith
  have hs : 0 < Real.sqrt (2 * (1 - n)) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * (1 - n) by positivity)
  have hsle : Real.sqrt (2 * (1 - n)) ≤ v + n - 1 := by linarith
  have hsqle : (Real.sqrt (2 * (1 - n))) ^ 2 ≤ (v + n - 1) ^ 2 :=
    (sq_le_sq₀ hs.le (by linarith)).mpr hsle
  have hD : 0 ≤ (v + n) ^ 2 - 2 * v - 1 := by nlinarith
  have hd0 : 0 ≤ sourceOrder n v := Real.sqrt_nonneg _
  have hdsq : (sourceOrder n v) ^ 2 = (v + n) ^ 2 - 2 * v - 1 :=
    Real.sq_sqrt hD
  have hv0 : 0 < v := by linarith
  have hgap : 0 < (1 - n) * (2 * v + n + 1) := by
    apply mul_pos hp
    linarith
  refine ⟨hd0, ?_, ?_⟩
  · nlinarith
  · linarith

theorem source_conjecture_339406_lower : SourceClaim339406Lower := by
  intro n v hn hv x hx
  obtain ⟨hd0, hdv, hm⟩ := source_parameter_geometry hn hv
  exact tail_strict_lower_bound hx hd0 hdv hm

end GauntIntegral
