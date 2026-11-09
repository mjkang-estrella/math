import RealBridge
open KirchhoffReal
-- Independent spelling of the two universal claims, including all quantifiers.
def ReviewerClaim (Inv : {n : ℕ} → Mat n → Mat n → Prop)
    (R : {n : ℕ} → Mat n → ℝ) : Prop :=
  ∀ (n : ℕ), n ≥ 2 → ∀ (g : Kirchhoff.Graph n), g.simple.Connected →
    ∀ a : ℤ, (a = 1 ∨ a = -1) →
      ∃ B C : Mat n,
        Inv (liftQ (Kirchhoff.laplacian g 0)) B ∧
        Inv (liftQ (Kirchhoff.laplacian g a)) C ∧
        (if a = 1 then R B ≤ R C else R C ≤ R B) ∧
        (R C = R B ↔ ∃ d, ∀ i, Kirchhoff.degree g i = d)
theorem reviewer_mp : ¬ ReviewerClaim @Penrose @pairIndex := by
  exact refuteMP
theorem reviewer_spectral : ¬ ReviewerClaim @GroupInverse @spectralIndex := by
  exact refuteSpec
#print axioms reviewer_mp
#print axioms reviewer_spectral
