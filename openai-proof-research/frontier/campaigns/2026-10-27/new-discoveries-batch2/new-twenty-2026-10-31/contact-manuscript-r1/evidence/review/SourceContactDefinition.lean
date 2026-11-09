import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

namespace ContactReview

/-- Literal local zero-set comparison in the bidisk. `q` must be the
reflection of the reduced stable denominator, up to a nonzero local unit.
Certification of that connection is a separate mandatory theorem. -/
def HasZeroSetContact (q : ℂ → ℂ → ℂ) (τ₁ τ₂ : ℂ) (K : ℕ) : Prop :=
  ‖τ₁‖ = 1 ∧ ‖τ₂‖ = 1 ∧ q τ₁ τ₂ = 0 ∧
  ∃ δ ρ c C : ℝ, 0 < δ ∧ 0 < ρ ∧ 0 < c ∧ 0 < C ∧
    ∀ z : ℂ, ‖z‖ = 1 → 0 < ‖z - τ₁‖ → ‖z - τ₁‖ < δ →
      (∀ v : ℂ, ‖v‖ < 1 → ‖v - τ₂‖ < ρ → q z v = 0 →
        c * ‖z - τ₁‖ ^ K ≤ 1 - ‖v‖) ∧
      (∃ v : ℂ, ‖v‖ < 1 ∧ ‖v - τ₂‖ < ρ ∧ q z v = 0 ∧
        1 - ‖v‖ ≤ C * ‖z - τ₁‖ ^ K)

/-- Upper-half-plane version for the reduced denominator of beta(f(-1/x,w)).
The two clauses express the lower bound for every local zero and an upper
bound attained by some local zero, avoiding an empty-set infimum. -/
def HasHalfPlaneContact (r : ℂ → ℂ → ℂ) (K : ℕ) : Prop :=
  r 0 0 = 0 ∧
  ∃ δ ρ c C : ℝ, 0 < δ ∧ 0 < ρ ∧ 0 < c ∧ 0 < C ∧
    ∀ x : ℝ, 0 < |x| → |x| < δ →
      (∀ w : ℂ, ‖w‖ < ρ → w.im < 0 → r x w = 0 →
        c * |x| ^ K ≤ |w.im|) ∧
      (∃ w : ℂ, ‖w‖ < ρ ∧ w.im < 0 ∧ r x w = 0 ∧
        |w.im| ≤ C * |x| ^ K)

end ContactReview
