import ContactExclusion
namespace ContactPilot
noncomputable section

def HasLocalZeroSetContact (q : ℂ → ℂ → ℂ) (τ₁ τ₂ : ℂ) (K : ℕ) : Prop :=
  ‖τ₁‖ = 1 ∧ ‖τ₂‖ = 1 ∧ q τ₁ τ₂ = 0 ∧
  ∃ c C ρ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ρ₀ ∧
    (∃ δ₀ > 0, ∀ z : ℂ, ‖z‖ = 1 → 0 < ‖z - τ₁‖ → ‖z - τ₁‖ < δ₀ →
      ∀ v : ℂ, ‖v‖ < 1 → ‖v - τ₂‖ < ρ₀ → q z v = 0 →
        c * ‖z - τ₁‖ ^ K ≤ 1 - ‖v‖) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ δ > 0, ∀ z : ℂ,
      ‖z‖ = 1 → 0 < ‖z - τ₁‖ → ‖z - τ₁‖ < δ →
      ∃ v : ℂ, ‖v‖ < 1 ∧ ‖v - τ₂‖ < ρ ∧ q z v = 0 ∧
        1 - ‖v‖ ≤ C * ‖z - τ₁‖ ^ K)

def SourceConjectureLocal : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (isZ : Fin n → Bool) (i : Fin n)
    (cert : ReducedCertificate (graphFunction G isZ i)) (d K : ℕ),
    NearestWDistance G isZ i d → 0 < K → Even K →
    HasLocalZeroSetContact (eval₂ cert.numerator) (-1) 1 K → K = 2*d
end
end ContactPilot
