import FamilyAssembly
set_option autoImplicit false
namespace Polyomino57
inductive RowFamilyTree where
  | leaf (rows : Array (List GridPoint))
  | branch (left right : RowFamilyTree)
def FamilyMember (row : List GridPoint) : RowFamilyTree → Prop
  | .leaf rows => row ∈ rows.toList
  | .branch left right => FamilyMember row left ∨ FamilyMember row right
def familyLookup : RowFamilyTree → List Bool → ℕ → Option (List GridPoint)
  | .leaf rows, [], i => rows[i]?
  | .branch left right, b :: bs, i => familyLookup (if b then right else left) bs i
  | _, _, _ => none

theorem familyLookup_sound (T : RowFamilyTree) (path : List Bool) (i : ℕ)
    (row : List GridPoint) (h : familyLookup T path i = some row) : FamilyMember row T := by
  induction T generalizing path with
  | leaf rows =>
    cases path with
    | nil =>
      simp only [familyLookup] at h
      exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? h)
    | cons b bs => simp [familyLookup] at h
  | branch left right ihl ihr =>
    cases path with
    | nil => simp [familyLookup] at h
    | cons b bs =>
      cases b with
      | false => exact Or.inl (ihl bs h)
      | true => exact Or.inr (ihr bs h)

theorem familyRowClosed_of_paths (T : RowFamilyTree) (row : List GridPoint)
    (next : Array (List GridPoint)) (choice : GridPoint → ℕ × GridPoint)
    (paths : ∀ S ∈ next.toList, ∃ path i, familyLookup T path i = some S)
    (checked : successorFastRowCheck next row choice = true) :
    FamilyRowClosed (fun S => FamilyMember S T) row := by
  refine ⟨next,choice,?_,checked⟩
  intro S hS
  obtain ⟨path,i,hi⟩ := paths S hS
  exact familyLookup_sound T path i S hi
end Polyomino57
