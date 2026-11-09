import PDTAR.CoreProofFinal
import PDTAR.SmallObligations
namespace PDTAR
open Finset
def leftPart (s t : ℕ) : Finset (Fin s ⊕ Fin t) :=
  univ.map ⟨Sum.inl, Sum.inl_injective⟩
def rightPart (s t : ℕ) : Finset (Fin s ⊕ Fin t) :=
  univ.map ⟨Sum.inr, Sum.inr_injective⟩

theorem sum_parts (s t : ℕ) :
    CompleteBetween (completeBipartiteGraph (Fin s) (Fin t)) (leftPart s t) (rightPart s t) := by
  constructor
  · constructor
    · apply disjoint_left.mpr
      intro x
      cases x <;> simp [leftPart,rightPart]
    · ext x
      cases x <;> simp [leftPart,rightPart]
  · intro x y
    cases x <;> cases y <;> simp [completeBipartiteGraph,leftPart,rightPart]

theorem sum_noIsolated (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    NoIsolated (completeBipartiteGraph (Fin s) (Fin t)) := by
  intro x
  cases x with
  | inl a => exact ⟨Sum.inr ⟨0,by omega⟩,by simp [completeBipartiteGraph]⟩
  | inr b => exact ⟨Sum.inl ⟨0,by omega⟩,by simp [completeBipartiteGraph]⟩

end PDTAR
