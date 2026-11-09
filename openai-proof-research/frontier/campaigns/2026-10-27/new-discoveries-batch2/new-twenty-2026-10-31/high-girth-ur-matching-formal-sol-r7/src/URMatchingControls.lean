module
public import URMatchingDeletion
@[expose] public section
namespace URMatching.Controls
abbrev K2 : SimpleGraph (Fin 2) := ⊤
def edge : Finset (Sym2 (Fin 2)) := {s(0, 1)}
theorem edge_isMatching : IsMatching K2 edge := by
  simp [IsMatching, edge]
theorem edge_nonempty : edge.card = 1 := by simp [edge]
theorem empty_graph_matchingNumber : matchingNumber (⊥ : SimpleGraph (Fin 2)) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (matchingNumber_le_iff _ _).mpr
  intro M hm
  have he : M = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    simpa using hm.1 e he
  simp [he]
end URMatching.Controls
