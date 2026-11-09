import Efficient
set_option autoImplicit false
namespace Polyomino57
inductive PlacementTree where
  | leaf (rows : List (List GridPoint × GridPoint))
  | branch (left right : PlacementTree)
def treeCheck : PlacementTree → Bool
  | .leaf rows => numericBatch rows
  | .branch left right => treeCheck left && treeCheck right
def TreeMember (row : List GridPoint × GridPoint) : PlacementTree → Prop
  | .leaf rows => row ∈ rows
  | .branch left right => TreeMember row left ∨ TreeMember row right

theorem treeCheck_sound (T : PlacementTree) (h : treeCheck T = true) :
    ∀ row, TreeMember row T → translate row.2 row.1.toFinset ⊆ witness := by
  induction T with
  | leaf rows => exact fun row hr => numericBatch_sound rows h row hr
  | branch left right ihl ihr =>
    change (treeCheck left && treeCheck right) = true at h
    simp only [Bool.and_eq_true] at h
    have hh := h
    intro row hr
    exact hr.elim (ihl hh.1 row) (ihr hh.2 row)
end Polyomino57
