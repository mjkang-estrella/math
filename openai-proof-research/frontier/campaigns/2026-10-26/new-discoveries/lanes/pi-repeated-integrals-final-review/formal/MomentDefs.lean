import Mathlib

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology

namespace RepeatedIntegrals

noncomputable section

abbrev MomentSpace (n : ℕ) := Fin (n + 1) → ℝ

def momentCurve (n : ℕ) (t : ℝ) : MomentSpace n := fun i => t ^ i.val

def densityMoments (n : ℕ) (ρ : ℝ → ℝ) : MomentSpace n :=
  fun i => ∫ t in (0 : ℝ)..1, t ^ i.val * ρ t

def GoodDensity (ρ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ρ ∧
  (∀ t ∈ Icc (0 : ℝ) 1, 0 < ρ t) ∧
  (ρ =ᶠ[𝓝 (0 : ℝ)] fun _ => 1) ∧
  (ρ =ᶠ[𝓝 (1 : ℝ)] fun _ => 1)

def smoothMomentSet (n : ℕ) : Set (MomentSpace n) :=
  {y | ∃ ρ : ℝ → ℝ, GoodDensity ρ ∧ densityMoments n ρ = y}

theorem goodDensity_one : GoodDensity (fun _ : ℝ => 1) := by
  exact ⟨contDiff_const, by intro t ht; norm_num, Filter.EventuallyEq.rfl,
    Filter.EventuallyEq.rfl⟩

theorem smoothMomentSet_nonempty (n : ℕ) : (smoothMomentSet n).Nonempty := by
  exact ⟨densityMoments n (fun _ => 1), fun _ => 1, goodDensity_one, rfl⟩

end

end RepeatedIntegrals
