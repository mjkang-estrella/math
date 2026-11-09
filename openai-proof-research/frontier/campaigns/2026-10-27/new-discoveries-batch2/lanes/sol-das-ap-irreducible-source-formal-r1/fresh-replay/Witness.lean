import Definitions
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Das
-- Coordinates in this file are zero based.
def witness : Pattern 5 := fun i j =>
  match i.val, j.val with
  | 0, 1 | 0, 4 | 1, 0 | 2, 3 | 3, 2 | 4, 2 => Sign.plus
  | 1, 4 | 3, 4 | 4, 1 | 4, 3 => Sign.minus
  | _, _ => Sign.zero
theorem witness_AP : APIrreducible witness := by decide
theorem witness_deletions : ∀ i j, witness i j ≠ Sign.zero →
    ¬ APIrreducible (erase witness i j) := by decide
-- The six positive deletions destroy their specified row or column.
theorem plus_obstructions :
    (¬ ∃ i, erase witness 0 1 i 1 = Sign.plus) ∧
    (¬ ∃ j, erase witness 1 0 1 j = Sign.plus) ∧
    (¬ ∃ j, erase witness 2 3 2 j = Sign.plus) ∧
    (¬ ∃ j, erase witness 3 2 3 j = Sign.plus) ∧
    (¬ ∃ i, erase witness 0 4 i 4 = Sign.plus) ∧
    (¬ ∃ j, erase witness 4 2 4 j = Sign.plus) := by decide
-- The four negative deletions use the recomputed A or B outgoing block.
theorem minus_obstructions :
    (∀ i ∈ ({2,3} : Finset (Fin 5)), ∀ j ∉ ({2,3} : Finset (Fin 5)),
      erase witness 3 4 i j = Sign.zero) ∧
    (∀ i ∈ ({2,3} : Finset (Fin 5)), ∀ j ∉ ({2,3} : Finset (Fin 5)),
      B (erase witness 4 3) i j = 0) ∧
    (∀ i ∈ ({2,3,4} : Finset (Fin 5)), ∀ j ∉ ({2,3,4} : Finset (Fin 5)),
      erase witness 4 1 i j = Sign.zero) ∧
    (∀ i ∈ ({2,3,4} : Finset (Fin 5)), ∀ j ∉ ({2,3,4} : Finset (Fin 5)),
      B (erase witness 1 4) i j = 0) := by decide
theorem witness_minimal : MinimalAP witness := ⟨witness_AP, witness_deletions⟩
theorem witness_diagonal : ZeroDiagonal witness := by unfold ZeroDiagonal; decide
theorem witness_count : nonzeros witness = 10 := by decide
theorem ten_gt_eight : 10 > 2*5-2 := by decide
theorem literal_counterexample : ∃ A : Pattern 5,
    ZeroDiagonal A ∧ MinimalAP A ∧ nonzeros A > 2*5-2 := by
  exact ⟨witness, witness_diagonal, witness_minimal, witness_count ▸ ten_gt_eight⟩
theorem literal_conjecture51_false : ¬ SourceConjecture := by
  intro h
  have hb := h 5 (by decide) witness witness_diagonal witness_minimal
  rw [witness_count] at hb
  exact (by decide : ¬ (10 ≤ 2*5-2)) hb
theorem literal_universal_bound_false : ¬ (∀ n : ℕ, 0 < n → ∀ A : Pattern n,
    ZeroDiagonal A → MinimalAP A → nonzeros A ≤ 2*n-2) :=
  literal_conjecture51_false
end Das
