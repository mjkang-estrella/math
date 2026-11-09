import FiniteBridge
set_option autoImplicit false
namespace Polyomino57.Diagonal.FiniteProof
open Polyomino57
def CutGood (P S : Finset GridPoint) : Prop :=
  S.Nonempty ∧ S ⊆ P ∧ S ≠ P ∧ ∀ a ∈ S, ∀ b ∈ P, b ∉ S → ¬ Adj a b
instance (P S : Finset GridPoint) : Decidable (CutGood P S) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
theorem not_connected_of_cut {P S : Finset GridPoint} (h : CutGood P S) : ¬ EdgeConnected P := by
  intro hc
  obtain ⟨a,ha,b,hb,hbs,hadj⟩ := boundary hc h.1 h.2.1 h.2.2.1
  exact h.2.2.2 a ha b hb hbs hadj
end Polyomino57.Diagonal.FiniteProof
