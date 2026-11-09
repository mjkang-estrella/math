import Sigma.Endpoint
namespace Review
open Sigma365710
def p4 : SimpleGraph (Fin 4) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := ⟨by intros; tauto⟩
  loopless := ⟨by intro; omega⟩
instance : DecidableRel p4.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
example : sigmaT p4 = 4 := by decide
example : sigmaT (completeBipartite 4 1) = 12 := by decide
example : sigmaT (completeBipartite 4 2) = 0 := by decide
example : sigmaT p4 ≠ 2 := by decide
example : sigmaT p4 ≠ 8 := by decide
example : sigmaT (completeBipartite 1 0) = 0 := by decide
example : ¬ HasCompleteBipartition p4 := by
  rintro ⟨S,h⟩
  have h01 := (h 0 1).mp (show p4.Adj 0 1 by decide)
  have h12 := (h 1 2).mp (show p4.Adj 1 2 by decide)
  have h23 := (h 2 3).mp (show p4.Adj 2 3 by decide)
  have h03 := (h 0 3).not.mp (show ¬ p4.Adj 0 3 by decide)
  tauto
example : F 4 3 = 12 := by decide
example : ((3 : ℤ) * (4 - 3) * ((4 - 2 * 3 : ℕ) : ℤ)^2) = 0 := by decide
theorem decider_independent {n : ℕ} (G : SimpleGraph (Fin n))
    (d₁ d₂ : DecidableRel G.Adj) : @sigmaT n G d₁ = @sigmaT n G d₂ := by
  have : d₁ = d₂ := Subsingleton.elim _ _
  cases this
  rfl
end Review
