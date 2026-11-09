import SortedCertificate
import PlacementTree
set_option autoImplicit false
namespace Polyomino57
-- The existential choice is selected only in a proof; it is never kernel-evaluated.
def LocallyClosed (A B : Array (List GridPoint)) : Prop :=
  ∀ row ∈ A.toList, ∃ choice : GridPoint → ℕ × GridPoint,
    successorFastRowCheck B row choice = true

theorem locallyClosed_array {A B : Array (List GridPoint)} (h : LocallyClosed A B) :
    ∃ choices, arrayClosureCheck A B choices = true := by
  classical
  have hh : ∀ row, ∃ choice : GridPoint → ℕ × GridPoint,
      row ∈ A.toList → successorRowCheck B row choice = true := by
    intro row
    by_cases hr : row ∈ A.toList
    · obtain ⟨choice,hc⟩ := h row hr
      exact ⟨choice, fun _ => successorFastRowCheck_implies B row choice hc⟩
    · exact ⟨fun _ => (0,(0,0)), fun ha => False.elim (hr ha)⟩
  choose choices hc using hh
  exact ⟨choices,List.all_eq_true.mpr hc⟩

-- Transfer an actual literal placement to any representative having the same
-- normalization. No equality of the two coordinate lists is assumed.
theorem placement_of_normalized_row (P : Finset GridPoint) (hP : P.Nonempty)
    (row : List GridPoint × GridPoint) (hr : row.1.toFinset.Nonempty)
    (he : normalize P hP = normalize row.1.toFinset hr)
    (hs : translate row.2 row.1.toFinset ⊆ witness) :
    ∃ t, translate t P ⊆ witness := by
  obtain ⟨t,ht⟩ := equal_normalizations_are_translates P row.1.toFinset hP hr he
  refine ⟨(t.1+row.2.1,t.2+row.2.2),?_⟩
  rw [← translate_comp,ht]
  exact hs

theorem placement_of_tree_normalization (T : PlacementTree) (hc : treeCheck T = true)
    (P : Finset GridPoint) (hP : P.Nonempty)
    (row : List GridPoint × GridPoint) (hm : TreeMember row T)
    (hr : row.1.toFinset.Nonempty)
    (he : normalize P hP = normalize row.1.toFinset hr) :
    ∃ t, translate t P ⊆ witness :=
  placement_of_normalized_row P hP row hr he (treeCheck_sound T hc row hm)
end Polyomino57
