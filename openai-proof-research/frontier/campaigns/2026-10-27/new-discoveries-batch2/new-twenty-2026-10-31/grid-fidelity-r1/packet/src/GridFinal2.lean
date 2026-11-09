module
public import GridTransport
public import GridChecks
public import GridRegression
@[expose] public section

namespace GridFinal2
open Grid343536

/-- The negative half of the full stabilizer classification is unconditional. -/
theorem free_implies_nonexceptional (m n : ℕ) (hf : HasFreeVertex (G m n)) :
    ¬ (2 ≤ m ∧ m = n ∧ n ≤ 3) := by
  rintro ⟨hm, rfl, hn⟩
  have h : m = 2 ∨ m = 3 := by omega
  rcases h with rfl | rfl
  · exact nofree_two hf
  · exact nofree_three hf

/-- The supplied lattice structure uses the inherited source refinement order. -/
noncomputable abbrev equitableLattice (m n : ℕ) : CompleteLattice (EqPart (G m n)) :=
  inferInstance

/-- Conditional handback only. All three unclosed obligations remain explicit premises. -/
theorem mathdb_343536 (main : MainOrbit) (free : FreeClassification)
    (exceptional : ExceptionalNoIso) :
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (∀ r : Setoid (Fin m × Fin n),
        IsEquitable (G m n) r ↔
          ∃ H : Subgroup (G m n ≃g G m n), r = orbitSetoid (G m n) H) ∧
      (Nonempty (EqPart (G m n) ≃o Subgroup (G m n ≃g G m n)) ↔
        HasFreeVertex (G m n)) ∧
      (HasFreeVertex (G m n) ↔ ¬ (2 ≤ m ∧ m = n ∧ n ≤ 3)) :=
  Grid343536.mathdb_343536 main free exceptional
end GridFinal2
