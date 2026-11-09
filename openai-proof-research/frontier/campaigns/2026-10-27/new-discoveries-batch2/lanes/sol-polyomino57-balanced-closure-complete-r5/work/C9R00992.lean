import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R00992G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r992_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r992targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r992choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r992targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r992choice = true := by decide
    refine ⟨c9r992targets, c9r992choice, ?_, checked⟩
    intro S h
    simp only [c9r992targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 23 _ (by rfl)
  have c9r993_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)] := by
    let c9r993targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c9r993choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r993targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)] c9r993choice = true := by decide
    refine ⟨c9r993targets, c9r993choice, ?_, checked⟩
    intro S h
    simp only [c9r993targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 26 _ (by rfl)
  have c9r994_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)] := by
    let c9r994targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)]]
    let c9r994choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,1),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r994targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)] c9r994choice = true := by decide
    refine ⟨c9r994targets, c9r994choice, ?_, checked⟩
    intro S h
    simp only [c9r994targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 29 _ (by rfl)
  have c9r995_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)] := by
    let c9r995targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)]]
    let c9r995choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,0),(13,(0,0))),((4,2),(14,(0,0))),((5,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r995targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)] c9r995choice = true := by decide
    refine ⟨c9r995targets, c9r995choice, ?_, checked⟩
    intro S h
    simp only [c9r995targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 0 _ (by rfl)
  have c9r996_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)] := by
    let c9r996targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c9r996choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r996targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)] c9r996choice = true := by decide
    refine ⟨c9r996targets, c9r996choice, ?_, checked⟩
    intro S h
    simp only [c9r996targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 3 _ (by rfl)
  have c9r997_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)] := by
    let c9r997targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c9r997choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r997targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)] c9r997choice = true := by decide
    refine ⟨c9r997targets, c9r997choice, ?_, checked⟩
    intro S h
    simp only [c9r997targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 6 _ (by rfl)
  have c9r998_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)] := by
    let c9r998targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c9r998choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,5),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r998targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)] c9r998choice = true := by decide
    refine ⟨c9r998targets, c9r998choice, ?_, checked⟩
    intro S h
    simp only [c9r998targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 9 _ (by rfl)
  have c9r999_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)] := by
    let c9r999targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c9r999choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0))),((4,4),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r999targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)] c9r999choice = true := by decide
    refine ⟨c9r999targets, c9r999choice, ?_, checked⟩
    intro S h
    simp only [c9r999targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 12 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r992_closed
  · subst row; exact c9r993_closed
  · subst row; exact c9r994_closed
  · subst row; exact c9r995_closed
  · subst row; exact c9r996_closed
  · subst row; exact c9r997_closed
  · subst row; exact c9r998_closed
  · subst row; exact c9r999_closed
theorem C9R00992G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1000_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r1000targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r1000choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1000targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)] c9r1000choice = true := by decide
    refine ⟨c9r1000targets, c9r1000choice, ?_, checked⟩
    intro S h
    simp only [c9r1000targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 17 _ (by rfl)
  have c9r1001_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)] := by
    let c9r1001targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
    let c9r1001choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1001targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)] c9r1001choice = true := by decide
    refine ⟨c9r1001targets, c9r1001choice, ?_, checked⟩
    intro S h
    simp only [c9r1001targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 19 _ (by rfl)
  have c9r1002_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c9r1002targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c9r1002choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1002targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)] c9r1002choice = true := by decide
    refine ⟨c9r1002targets, c9r1002choice, ?_, checked⟩
    intro S h
    simp only [c9r1002targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 21 _ (by rfl)
  have c9r1003_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)] := by
    let c9r1003targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c9r1003choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1003targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)] c9r1003choice = true := by decide
    refine ⟨c9r1003targets, c9r1003choice, ?_, checked⟩
    intro S h
    simp only [c9r1003targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 25 _ (by rfl)
  have c9r1004_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)] := by
    let c9r1004targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c9r1004choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1004targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)] c9r1004choice = true := by decide
    refine ⟨c9r1004targets, c9r1004choice, ?_, checked⟩
    intro S h
    simp only [c9r1004targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 28 _ (by rfl)
  have c9r1005_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)] := by
    let c9r1005targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c9r1005choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1005targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)] c9r1005choice = true := by decide
    refine ⟨c9r1005targets, c9r1005choice, ?_, checked⟩
    intro S h
    simp only [c9r1005targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 30 _ (by rfl)
  have c9r1006_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c9r1006targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c9r1006choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1006targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)] c9r1006choice = true := by decide
    refine ⟨c9r1006targets, c9r1006choice, ?_, checked⟩
    intro S h
    simp only [c9r1006targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 1 _ (by rfl)
  have c9r1007_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)] := by
    let c9r1007targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)]]
    let c9r1007choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1007targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)] c9r1007choice = true := by decide
    refine ⟨c9r1007targets, c9r1007choice, ?_, checked⟩
    intro S h
    simp only [c9r1007targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1000_closed
  · subst row; exact c9r1001_closed
  · subst row; exact c9r1002_closed
  · subst row; exact c9r1003_closed
  · subst row; exact c9r1004_closed
  · subst row; exact c9r1005_closed
  · subst row; exact c9r1006_closed
  · subst row; exact c9r1007_closed
theorem C9R00992G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1008_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)] := by
    let c9r1008targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)]]
    let c9r1008choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,2),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1008targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)] c9r1008choice = true := by decide
    refine ⟨c9r1008targets, c9r1008choice, ?_, checked⟩
    intro S h
    simp only [c9r1008targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 7 _ (by rfl)
  have c9r1009_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)] := by
    let c9r1009targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c9r1009choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,5),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1009targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)] c9r1009choice = true := by decide
    refine ⟨c9r1009targets, c9r1009choice, ?_, checked⟩
    intro S h
    simp only [c9r1009targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 11 _ (by rfl)
  have c9r1010_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)] := by
    let c9r1010targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c9r1010choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1010targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)] c9r1010choice = true := by decide
    refine ⟨c9r1010targets, c9r1010choice, ?_, checked⟩
    intro S h
    simp only [c9r1010targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 14 _ (by rfl)
  have c9r1011_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)] := by
    let c9r1011targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c9r1011choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1011targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)] c9r1011choice = true := by decide
    refine ⟨c9r1011targets, c9r1011choice, ?_, checked⟩
    intro S h
    simp only [c9r1011targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 16 _ (by rfl)
  have c9r1012_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)] := by
    let c9r1012targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c9r1012choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1012targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)] c9r1012choice = true := by decide
    refine ⟨c9r1012targets, c9r1012choice, ?_, checked⟩
    intro S h
    simp only [c9r1012targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 20 _ (by rfl)
  have c9r1013_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)] := by
    let c9r1013targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c9r1013choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,4),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1013targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)] c9r1013choice = true := by decide
    refine ⟨c9r1013targets, c9r1013choice, ?_, checked⟩
    intro S h
    simp only [c9r1013targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 23 _ (by rfl)
  have c9r1014_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)] := by
    let c9r1014targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c9r1014choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,3),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1014targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)] c9r1014choice = true := by decide
    refine ⟨c9r1014targets, c9r1014choice, ?_, checked⟩
    intro S h
    simp only [c9r1014targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 26 _ (by rfl)
  have c9r1015_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)] := by
    let c9r1015targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c9r1015choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,4),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1015targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)] c9r1015choice = true := by decide
    refine ⟨c9r1015targets, c9r1015choice, ?_, checked⟩
    intro S h
    simp only [c9r1015targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1008_closed
  · subst row; exact c9r1009_closed
  · subst row; exact c9r1010_closed
  · subst row; exact c9r1011_closed
  · subst row; exact c9r1012_closed
  · subst row; exact c9r1013_closed
  · subst row; exact c9r1014_closed
  · subst row; exact c9r1015_closed
theorem C9R00992G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1016_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r1016targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r1016choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1016targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] c9r1016choice = true := by decide
    refine ⟨c9r1016targets, c9r1016choice, ?_, checked⟩
    intro S h
    simp only [c9r1016targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 6 _ (by rfl)
  have c9r1017_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r1017targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r1017choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1017targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] c9r1017choice = true := by decide
    refine ⟨c9r1017targets, c9r1017choice, ?_, checked⟩
    intro S h
    simp only [c9r1017targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 9 _ (by rfl)
  have c9r1018_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r1018targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r1018choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1018targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] c9r1018choice = true := by decide
    refine ⟨c9r1018targets, c9r1018choice, ?_, checked⟩
    intro S h
    simp only [c9r1018targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 11 _ (by rfl)
  have c9r1019_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r1019targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r1019choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1019targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)] c9r1019choice = true := by decide
    refine ⟨c9r1019targets, c9r1019choice, ?_, checked⟩
    intro S h
    simp only [c9r1019targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 13 _ (by rfl)
  have c9r1020_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r1020targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r1020choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1020targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)] c9r1020choice = true := by decide
    refine ⟨c9r1020targets, c9r1020choice, ?_, checked⟩
    intro S h
    simp only [c9r1020targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 16 _ (by rfl)
  have c9r1021_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r1021targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r1021choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,-1),(13,(0,1))),((5,1),(14,(0,0))),((6,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1021targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)] c9r1021choice = true := by decide
    refine ⟨c9r1021targets, c9r1021choice, ?_, checked⟩
    intro S h
    simp only [c9r1021targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 18 _ (by rfl)
  have c9r1022_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r1022targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r1022choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1022targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)] c9r1022choice = true := by decide
    refine ⟨c9r1022targets, c9r1022choice, ?_, checked⟩
    intro S h
    simp only [c9r1022targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 21 _ (by rfl)
  have c9r1023_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r1023targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r1023choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,2),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1023targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)] c9r1023choice = true := by decide
    refine ⟨c9r1023targets, c9r1023choice, ?_, checked⟩
    intro S h
    simp only [c9r1023targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1016_closed
  · subst row; exact c9r1017_closed
  · subst row; exact c9r1018_closed
  · subst row; exact c9r1019_closed
  · subst row; exact c9r1020_closed
  · subst row; exact c9r1021_closed
  · subst row; exact c9r1022_closed
  · subst row; exact c9r1023_closed
theorem C9R00992_closed (row : List GridPoint) (h : FamilyMember row F9B000L31) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L31, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R00992G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00992G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00992G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00992G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00992G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00992G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00992G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00992G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00992G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00992G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00992G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00992G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00992G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00992G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00992G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00992G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00992G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00992G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00992G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00992G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00992G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00992G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00992G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00992G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00992G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00992G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00992G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00992G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00992G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00992G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00992G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00992G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
