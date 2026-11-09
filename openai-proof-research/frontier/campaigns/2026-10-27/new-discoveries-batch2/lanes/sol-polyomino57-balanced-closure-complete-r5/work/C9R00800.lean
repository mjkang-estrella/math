import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R00800G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r800_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(4,1)] := by
    let c9r800targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1)]]
    let c9r800choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,-1),(13,(0,1))),((4,2),(14,(0,0))),((5,0),(15,(0,0))),((5,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r800targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(4,1)] c9r800choice = true := by decide
    refine ⟨c9r800targets, c9r800choice, ?_, checked⟩
    intro S h
    simp only [c9r800targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 5 _ (by rfl)
  have c9r801_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(5,0)] := by
    let c9r801targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0)]]
    let c9r801choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,-1),(13,(0,1))),((4,1),(14,(0,0))),((5,-1),(15,(0,1))),((5,1),(16,(0,0))),((6,0),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r801targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(5,0)] c9r801choice = true := by decide
    refine ⟨c9r801targets, c9r801choice, ?_, checked⟩
    intro S h
    simp only [c9r801targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 7 _ (by rfl)
  have c9r802_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r802targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r802choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,5),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r802targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4)] c9r802choice = true := by decide
    refine ⟨c9r802targets, c9r802choice, ?_, checked⟩
    intro S h
    simp only [c9r802targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 12 _ (by rfl)
  have c9r803_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r803targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r803choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r803targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1)] c9r803choice = true := by decide
    refine ⟨c9r803targets, c9r803choice, ?_, checked⟩
    intro S h
    simp only [c9r803targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 16 _ (by rfl)
  have c9r804_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r804targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r804choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r804targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2)] c9r804choice = true := by decide
    refine ⟨c9r804targets, c9r804choice, ?_, checked⟩
    intro S h
    simp only [c9r804targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 18 _ (by rfl)
  have c9r805_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r805targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r805choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r805targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,3)] c9r805choice = true := by decide
    refine ⟨c9r805targets, c9r805choice, ?_, checked⟩
    intro S h
    simp only [c9r805targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 20 _ (by rfl)
  have c9r806_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r806targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r806choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r806targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,0),(3,1)] c9r806choice = true := by decide
    refine ⟨c9r806targets, c9r806choice, ?_, checked⟩
    intro S h
    simp only [c9r806targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 23 _ (by rfl)
  have c9r807_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2)] := by
    let c9r807targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c9r807choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r807targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2)] c9r807choice = true := by decide
    refine ⟨c9r807targets, c9r807choice, ?_, checked⟩
    intro S h
    simp only [c9r807targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 26 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r800_closed
  · subst row; exact c9r801_closed
  · subst row; exact c9r802_closed
  · subst row; exact c9r803_closed
  · subst row; exact c9r804_closed
  · subst row; exact c9r805_closed
  · subst row; exact c9r806_closed
  · subst row; exact c9r807_closed
theorem C9R00800G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r808_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(4,1)] := by
    let c9r808targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c9r808choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r808targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(4,1)] c9r808choice = true := by decide
    refine ⟨c9r808targets, c9r808choice, ?_, checked⟩
    intro S h
    simp only [c9r808targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 29 _ (by rfl)
  have c9r809_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3)] := by
    let c9r809targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c9r809choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r809targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3)] c9r809choice = true := by decide
    refine ⟨c9r809targets, c9r809choice, ?_, checked⟩
    intro S h
    simp only [c9r809targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 0 _ (by rfl)
  have c9r810_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(4,2)] := by
    let c9r810targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c9r810choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r810targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(4,2)] c9r810choice = true := by decide
    refine ⟨c9r810targets, c9r810choice, ?_, checked⟩
    intro S h
    simp only [c9r810targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 3 _ (by rfl)
  have c9r811_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r811targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r811choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,6),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0))),((3,5),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r811targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5)] c9r811choice = true := by decide
    refine ⟨c9r811targets, c9r811choice, ?_, checked⟩
    intro S h
    simp only [c9r811targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 8 _ (by rfl)
  have c9r812_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2)] := by
    let c9r812targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c9r812choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,5),(11,(0,0))),((3,1),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r812targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2)] c9r812choice = true := by decide
    refine ⟨c9r812targets, c9r812choice, ?_, checked⟩
    intro S h
    simp only [c9r812targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 12 _ (by rfl)
  have c9r813_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,3)] := by
    let c9r813targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c9r813choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,5),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r813targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,3)] c9r813choice = true := by decide
    refine ⟨c9r813targets, c9r813choice, ?_, checked⟩
    intro S h
    simp only [c9r813targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 14 _ (by rfl)
  have c9r814_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r814targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r814choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,5),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,5),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r814targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,4)] c9r814choice = true := by decide
    refine ⟨c9r814targets, c9r814choice, ?_, checked⟩
    intro S h
    simp only [c9r814targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 16 _ (by rfl)
  have c9r815_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2)] := by
    let c9r815targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c9r815choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r815targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2)] c9r815choice = true := by decide
    refine ⟨c9r815targets, c9r815choice, ?_, checked⟩
    intro S h
    simp only [c9r815targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r808_closed
  · subst row; exact c9r809_closed
  · subst row; exact c9r810_closed
  · subst row; exact c9r811_closed
  · subst row; exact c9r812_closed
  · subst row; exact c9r813_closed
  · subst row; exact c9r814_closed
  · subst row; exact c9r815_closed
theorem C9R00800G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r816_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3)] := by
    let c9r816targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c9r816choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r816targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3)] c9r816choice = true := by decide
    refine ⟨c9r816targets, c9r816choice, ?_, checked⟩
    intro S h
    simp only [c9r816targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 23 _ (by rfl)
  have c9r817_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(4,2)] := by
    let c9r817targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c9r817choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0))),((4,3),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r817targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(4,2)] c9r817choice = true := by decide
    refine ⟨c9r817targets, c9r817choice, ?_, checked⟩
    intro S h
    simp only [c9r817targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 26 _ (by rfl)
  have c9r818_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(3,4)] := by
    let c9r818targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c9r818choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,5),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r818targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(3,4)] c9r818choice = true := by decide
    refine ⟨c9r818targets, c9r818choice, ?_, checked⟩
    intro S h
    simp only [c9r818targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 29 _ (by rfl)
  have c9r819_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(4,3)] := by
    let c9r819targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c9r819choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0))),((4,4),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r819targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(4,3)] c9r819choice = true := by decide
    refine ⟨c9r819targets, c9r819choice, ?_, checked⟩
    intro S h
    simp only [c9r819targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 0 _ (by rfl)
  have c9r820_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r820targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r820choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,3),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r820targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2)] c9r820choice = true := by decide
    refine ⟨c9r820targets, c9r820choice, ?_, checked⟩
    intro S h
    simp only [c9r820targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 5 _ (by rfl)
  have c9r821_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3)] := by
    let c9r821targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c9r821choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,4),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r821targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3)] c9r821choice = true := by decide
    refine ⟨c9r821targets, c9r821choice, ?_, checked⟩
    intro S h
    simp only [c9r821targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 9 _ (by rfl)
  have c9r822_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,1)] := by
    let c9r822targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c9r822choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0))),((4,0),(13,(0,0))),((4,2),(14,(0,0))),((5,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r822targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,1)] c9r822choice = true := by decide
    refine ⟨c9r822targets, c9r822choice, ?_, checked⟩
    intro S h
    simp only [c9r822targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 12 _ (by rfl)
  have c9r823_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,2)] := by
    let c9r823targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c9r823choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0))),((4,3),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r823targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,2)] c9r823choice = true := by decide
    refine ⟨c9r823targets, c9r823choice, ?_, checked⟩
    intro S h
    simp only [c9r823targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r816_closed
  · subst row; exact c9r817_closed
  · subst row; exact c9r818_closed
  · subst row; exact c9r819_closed
  · subst row; exact c9r820_closed
  · subst row; exact c9r821_closed
  · subst row; exact c9r822_closed
  · subst row; exact c9r823_closed
theorem C9R00800G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r824_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(3,4)] := by
    let c9r824targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c9r824choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0))),((3,5),(13,(0,0))),((4,2),(14,(0,0))),((4,3),(15,(0,0))),((4,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r824targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(3,4)] c9r824choice = true := by decide
    refine ⟨c9r824targets, c9r824choice, ?_, checked⟩
    intro S h
    simp only [c9r824targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 18 _ (by rfl)
  have c9r825_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,2)] := by
    let c9r825targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c9r825choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,4),(12,(0,0))),((4,1),(13,(0,0))),((4,3),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r825targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,2)] c9r825choice = true := by decide
    refine ⟨c9r825targets, c9r825choice, ?_, checked⟩
    intro S h
    simp only [c9r825targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 21 _ (by rfl)
  have c9r826_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,3)] := by
    let c9r826targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c9r826choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0))),((4,4),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r826targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,3)] c9r826choice = true := by decide
    refine ⟨c9r826targets, c9r826choice, ?_, checked⟩
    intro S h
    simp only [c9r826targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 23 _ (by rfl)
  have c9r827_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,1),(4,2)] := by
    let c9r827targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c9r827choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,0),(13,(0,0))),((4,3),(14,(0,0))),((5,1),(15,(0,0))),((5,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r827targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,1),(4,2)] c9r827choice = true := by decide
    refine ⟨c9r827targets, c9r827choice, ?_, checked⟩
    intro S h
    simp only [c9r827targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 27 _ (by rfl)
  have c9r828_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(4,3)] := by
    let c9r828targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c9r828choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0))),((4,4),(14,(0,0))),((5,2),(15,(0,0))),((5,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r828targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(4,3)] c9r828choice = true := by decide
    refine ⟨c9r828targets, c9r828choice, ?_, checked⟩
    intro S h
    simp only [c9r828targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 30 _ (by rfl)
  have c9r829_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(5,2)] := by
    let c9r829targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c9r829choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0))),((4,3),(14,(0,0))),((5,1),(15,(0,0))),((5,3),(16,(0,0))),((6,2),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r829targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(5,2)] c9r829choice = true := by decide
    refine ⟨c9r829targets, c9r829choice, ?_, checked⟩
    intro S h
    simp only [c9r829targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 1 _ (by rfl)
  have c9r830_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r830targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r830choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r830targets [(0,0),(0,1),(0,2),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r830choice = true := by decide
    refine ⟨c9r830targets, c9r830choice, ?_, checked⟩
    intro S h
    simp only [c9r830targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 7 _ (by rfl)
  have c9r831_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r831targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r831choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,5),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0))),((3,3),(15,(0,0))),((3,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r831targets [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r831choice = true := by decide
    refine ⟨c9r831targets, c9r831choice, ?_, checked⟩
    intro S h
    simp only [c9r831targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,false,false] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r824_closed
  · subst row; exact c9r825_closed
  · subst row; exact c9r826_closed
  · subst row; exact c9r827_closed
  · subst row; exact c9r828_closed
  · subst row; exact c9r829_closed
  · subst row; exact c9r830_closed
  · subst row; exact c9r831_closed
theorem C9R00800_closed (row : List GridPoint) (h : FamilyMember row F9B000L25) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L25, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R00800G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00800G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00800G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00800G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00800G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00800G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00800G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00800G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00800G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00800G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00800G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00800G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00800G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00800G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00800G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00800G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00800G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00800G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00800G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00800G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00800G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00800G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00800G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00800G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00800G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00800G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00800G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00800G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00800G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00800G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00800G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00800G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
