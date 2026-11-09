import CrownVGraph
namespace CrownV
variable {n : ℕ}
open Classical

example {s : Finset (V n)} {t u : V n} (D : Finset (V n))
    (hDsub : ∀ z ∈ D, z ∈ s)
    (hcl : ∀ a ∈ D, ∀ ⦃b : V n⦄, SEdge (insert t s) a b → b ∈ D)
    : ∀ z : V n, SameC (insert t s) u z → z ∈ D → SameC s u z := by
  intro z h
  induction h with
  | refl => intro _; exact .refl
  | tail h₁ h₂ ih =>
    intro hzD
    have hmD := hcl _ hzD (sEdge_symm h₂)
    exact (ih hmD).trans (SameC.single ⟨hDsub _ hmD, hDsub _ hzD, h₂.2.2⟩)
end CrownV
