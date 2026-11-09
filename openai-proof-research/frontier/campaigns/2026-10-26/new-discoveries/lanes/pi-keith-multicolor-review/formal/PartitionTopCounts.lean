import Mathlib

namespace KeithMulticolor

/-- Ordinary weak unimodality on a finite ordered index set. -/
def Unimodal {n : ℕ} (f : Fin n → ℕ) : Prop :=
  ∃ peak : Fin n,
    (∀ i j, i ≤ j → j ≤ peak → f i ≤ f j) ∧
    (∀ i j, peak ≤ i → i ≤ j → f j ≤ f i)

end KeithMulticolor
