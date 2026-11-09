module
public import GridOrdinaryBorder
@[expose] public section
namespace GridFinal6
open Grid343536
/-- Unconditional literal MathDB 343536 endpoint for all positive grid dimensions. -/
theorem mathdb_343536 :
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (∀ r : Setoid (Fin m × Fin n),
        IsEquitable (G m n) r ↔
          ∃ H : Subgroup (G m n ≃g G m n), r = orbitSetoid (G m n) H) ∧
      (Nonempty (EqPart (G m n) ≃o Subgroup (G m n ≃g G m n)) ↔
        HasFreeVertex (G m n)) ∧
      (HasFreeVertex (G m n) ↔ ¬ (2 ≤ m ∧ m = n ∧ n ≤ 3)) :=
  GridFinal4.mathdb_343536 main_orbit_proved
end GridFinal6
#print axioms Grid343536.ordinary_border_transitivity
#print axioms Grid343536.main_orbit_proved
#print axioms GridFinal6.mathdb_343536
