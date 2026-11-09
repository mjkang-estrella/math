import PDTAR.Core
namespace PDTAR
open Finset

/-- Unproved reduction: relabel onto the target vertex type preserving every PD set. -/
def ReductionRemaining : Prop :=
  ∀ (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W), NoIsolated G → NoIsolated H →
    Nonempty (tar H ≃g tar G) →
    ∃ H' : SimpleGraph V, Nonempty (H ≃g H') ∧ SamePD G H'

/-- Unproved remainder of Core, beyond the compiled blocker and pair-fort lemmas. -/
def CoreRemaining : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (K H : SimpleGraph V) (A B : Finset V),
    CompleteBetween K A B → 3 ≤ A.card → 3 ≤ B.card →
    (A.card ≠ 3 ∨ B.card ≠ 3) → SamePD K H → H = K

def EdgeRemaining : Prop := TARUnique (completeBipartiteGraph (Fin 1) (Fin 1))
def StarsRemaining : Prop := ∀ t : ℕ, 3 ≤ t →
  TARUnique (completeBipartiteGraph (Fin 1) (Fin t)) ∧
  TARUnique (completeBipartiteGraph (Fin t) (Fin 1))
def ThreeThreeRemaining : Prop := TARUnique (completeBipartiteGraph (Fin 3) (Fin 3))
def TwoRemaining : Prop := ∀ s t : ℕ, 1 ≤ s → 1 ≤ t → (s = 2 ∨ t = 2) →
  ¬ TARUnique (completeBipartiteGraph (Fin s) (Fin t))
end PDTAR
