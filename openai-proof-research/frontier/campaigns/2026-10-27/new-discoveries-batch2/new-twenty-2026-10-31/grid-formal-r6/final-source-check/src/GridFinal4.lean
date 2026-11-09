module
public import GridOrbitSmall
@[expose] public section
namespace GridFinal4
open Grid343536
theorem exceptionalNoIso : ExceptionalNoIso := exceptional_no_iso

/-- Round 4 endpoint, retaining exactly MainOrbit. -/
theorem mathdb_343536 (main : MainOrbit) :
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (∀ r : Setoid (Fin m × Fin n),
        IsEquitable (G m n) r ↔
          ∃ H : Subgroup (G m n ≃g G m n), r = orbitSetoid (G m n) H) ∧
      (Nonempty (EqPart (G m n) ≃o Subgroup (G m n ≃g G m n)) ↔
        HasFreeVertex (G m n)) ∧
      (HasFreeVertex (G m n) ↔ ¬ (2 ≤ m ∧ m = n ∧ n ≤ 3)) :=
  Grid343536.mathdb_343536 main free_classification exceptional_no_iso
end GridFinal4
