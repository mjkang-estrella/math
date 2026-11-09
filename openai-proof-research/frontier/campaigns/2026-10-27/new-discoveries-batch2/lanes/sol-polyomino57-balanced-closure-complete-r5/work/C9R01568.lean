import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R01568G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1568_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)] := by
    let c9r1568targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)]]
    let c9r1568choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1568targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)] c9r1568choice = true := by decide
    refine ⟨c9r1568targets, c9r1568choice, ?_, checked⟩
    intro S h
    simp only [c9r1568targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 1 _ (by rfl)
  have c9r1569_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)] := by
    let c9r1569targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)]]
    let c9r1569choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1569targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)] c9r1569choice = true := by decide
    refine ⟨c9r1569targets, c9r1569choice, ?_, checked⟩
    intro S h
    simp only [c9r1569targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 4 _ (by rfl)
  have c9r1570_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)] := by
    let c9r1570targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c9r1570choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,5),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1570targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)] c9r1570choice = true := by decide
    refine ⟨c9r1570targets, c9r1570choice, ?_, checked⟩
    intro S h
    simp only [c9r1570targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 8 _ (by rfl)
  have c9r1571_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)] := by
    let c9r1571targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c9r1571choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1571targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)] c9r1571choice = true := by decide
    refine ⟨c9r1571targets, c9r1571choice, ?_, checked⟩
    intro S h
    simp only [c9r1571targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 11 _ (by rfl)
  have c9r1572_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)] := by
    let c9r1572targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c9r1572choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,4),(11,(0,0))),((5,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1572targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)] c9r1572choice = true := by decide
    refine ⟨c9r1572targets, c9r1572choice, ?_, checked⟩
    intro S h
    simp only [c9r1572targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 13 _ (by rfl)
  have c9r1573_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)] := by
    let c9r1573targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c9r1573choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1573targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)] c9r1573choice = true := by decide
    refine ⟨c9r1573targets, c9r1573choice, ?_, checked⟩
    intro S h
    simp only [c9r1573targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 17 _ (by rfl)
  have c9r1574_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)] := by
    let c9r1574targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c9r1574choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1574targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)] c9r1574choice = true := by decide
    refine ⟨c9r1574targets, c9r1574choice, ?_, checked⟩
    intro S h
    simp only [c9r1574targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 20 _ (by rfl)
  have c9r1575_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)] := by
    let c9r1575targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c9r1575choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1575targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)] c9r1575choice = true := by decide
    refine ⟨c9r1575targets, c9r1575choice, ?_, checked⟩
    intro S h
    simp only [c9r1575targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1568_closed
  · subst row; exact c9r1569_closed
  · subst row; exact c9r1570_closed
  · subst row; exact c9r1571_closed
  · subst row; exact c9r1572_closed
  · subst row; exact c9r1573_closed
  · subst row; exact c9r1574_closed
  · subst row; exact c9r1575_closed
theorem C9R01568G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1576_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)] := by
    let c9r1576targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c9r1576choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,4),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1576targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)] c9r1576choice = true := by decide
    refine ⟨c9r1576targets, c9r1576choice, ?_, checked⟩
    intro S h
    simp only [c9r1576targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 29 _ (by rfl)
  have c9r1577_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r1577targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r1577choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1577targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] c9r1577choice = true := by decide
    refine ⟨c9r1577targets, c9r1577choice, ?_, checked⟩
    intro S h
    simp only [c9r1577targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 3 _ (by rfl)
  have c9r1578_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r1578targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r1578choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1578targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] c9r1578choice = true := by decide
    refine ⟨c9r1578targets, c9r1578choice, ?_, checked⟩
    intro S h
    simp only [c9r1578targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 6 _ (by rfl)
  have c9r1579_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r1579targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r1579choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1579targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] c9r1579choice = true := by decide
    refine ⟨c9r1579targets, c9r1579choice, ?_, checked⟩
    intro S h
    simp only [c9r1579targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 8 _ (by rfl)
  have c9r1580_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r1580targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r1580choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1580targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)] c9r1580choice = true := by decide
    refine ⟨c9r1580targets, c9r1580choice, ?_, checked⟩
    intro S h
    simp only [c9r1580targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 10 _ (by rfl)
  have c9r1581_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r1581targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r1581choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1581targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)] c9r1581choice = true := by decide
    refine ⟨c9r1581targets, c9r1581choice, ?_, checked⟩
    intro S h
    simp only [c9r1581targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 13 _ (by rfl)
  have c9r1582_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r1582targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r1582choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1582targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)] c9r1582choice = true := by decide
    refine ⟨c9r1582targets, c9r1582choice, ?_, checked⟩
    intro S h
    simp only [c9r1582targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 15 _ (by rfl)
  have c9r1583_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r1583targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r1583choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1583targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)] c9r1583choice = true := by decide
    refine ⟨c9r1583targets, c9r1583choice, ?_, checked⟩
    intro S h
    simp only [c9r1583targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 18 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1576_closed
  · subst row; exact c9r1577_closed
  · subst row; exact c9r1578_closed
  · subst row; exact c9r1579_closed
  · subst row; exact c9r1580_closed
  · subst row; exact c9r1581_closed
  · subst row; exact c9r1582_closed
  · subst row; exact c9r1583_closed
theorem C9R01568G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1584_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r1584targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r1584choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1584targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)] c9r1584choice = true := by decide
    refine ⟨c9r1584targets, c9r1584choice, ?_, checked⟩
    intro S h
    simp only [c9r1584targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 21 _ (by rfl)
  have c9r1585_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r1585targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r1585choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,5),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1585targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)] c9r1585choice = true := by decide
    refine ⟨c9r1585targets, c9r1585choice, ?_, checked⟩
    intro S h
    simp only [c9r1585targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 26 _ (by rfl)
  have c9r1586_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r1586targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r1586choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1586targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)] c9r1586choice = true := by decide
    refine ⟨c9r1586targets, c9r1586choice, ?_, checked⟩
    intro S h
    simp only [c9r1586targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 30 _ (by rfl)
  have c9r1587_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r1587targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r1587choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1587targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)] c9r1587choice = true := by decide
    refine ⟨c9r1587targets, c9r1587choice, ?_, checked⟩
    intro S h
    simp only [c9r1587targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 0 _ (by rfl)
  have c9r1588_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r1588targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r1588choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1588targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)] c9r1588choice = true := by decide
    refine ⟨c9r1588targets, c9r1588choice, ?_, checked⟩
    intro S h
    simp only [c9r1588targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 2 _ (by rfl)
  have c9r1589_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r1589targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r1589choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1589targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)] c9r1589choice = true := by decide
    refine ⟨c9r1589targets, c9r1589choice, ?_, checked⟩
    intro S h
    simp only [c9r1589targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 5 _ (by rfl)
  have c9r1590_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r1590targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r1590choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1590targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)] c9r1590choice = true := by decide
    refine ⟨c9r1590targets, c9r1590choice, ?_, checked⟩
    intro S h
    simp only [c9r1590targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 8 _ (by rfl)
  have c9r1591_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r1591targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r1591choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1591targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)] c9r1591choice = true := by decide
    refine ⟨c9r1591targets, c9r1591choice, ?_, checked⟩
    intro S h
    simp only [c9r1591targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 11 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1584_closed
  · subst row; exact c9r1585_closed
  · subst row; exact c9r1586_closed
  · subst row; exact c9r1587_closed
  · subst row; exact c9r1588_closed
  · subst row; exact c9r1589_closed
  · subst row; exact c9r1590_closed
  · subst row; exact c9r1591_closed
theorem C9R01568G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1592_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r1592targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r1592choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1592targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)] c9r1592choice = true := by decide
    refine ⟨c9r1592targets, c9r1592choice, ?_, checked⟩
    intro S h
    simp only [c9r1592targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 14 _ (by rfl)
  have c9r1593_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r1593targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r1593choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1593targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)] c9r1593choice = true := by decide
    refine ⟨c9r1593targets, c9r1593choice, ?_, checked⟩
    intro S h
    simp only [c9r1593targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 17 _ (by rfl)
  have c9r1594_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r1594targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r1594choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1594targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)] c9r1594choice = true := by decide
    refine ⟨c9r1594targets, c9r1594choice, ?_, checked⟩
    intro S h
    simp only [c9r1594targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 22 _ (by rfl)
  have c9r1595_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r1595targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r1595choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1595targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] c9r1595choice = true := by decide
    refine ⟨c9r1595targets, c9r1595choice, ?_, checked⟩
    intro S h
    simp only [c9r1595targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 24 _ (by rfl)
  have c9r1596_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r1596targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r1596choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1596targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] c9r1596choice = true := by decide
    refine ⟨c9r1596targets, c9r1596choice, ?_, checked⟩
    intro S h
    simp only [c9r1596targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 26 _ (by rfl)
  have c9r1597_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r1597targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r1597choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,4),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1597targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)] c9r1597choice = true := by decide
    refine ⟨c9r1597targets, c9r1597choice, ?_, checked⟩
    intro S h
    simp only [c9r1597targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 30 _ (by rfl)
  have c9r1598_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r1598targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r1598choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1598targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)] c9r1598choice = true := by decide
    refine ⟨c9r1598targets, c9r1598choice, ?_, checked⟩
    intro S h
    simp only [c9r1598targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 1 _ (by rfl)
  have c9r1599_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r1599targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r1599choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1599targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)] c9r1599choice = true := by decide
    refine ⟨c9r1599targets, c9r1599choice, ?_, checked⟩
    intro S h
    simp only [c9r1599targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 3 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1592_closed
  · subst row; exact c9r1593_closed
  · subst row; exact c9r1594_closed
  · subst row; exact c9r1595_closed
  · subst row; exact c9r1596_closed
  · subst row; exact c9r1597_closed
  · subst row; exact c9r1598_closed
  · subst row; exact c9r1599_closed
theorem C9R01568_closed (row : List GridPoint) (h : FamilyMember row F9B000L49) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L49, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R01568G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01568G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01568G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01568G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01568G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01568G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01568G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01568G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01568G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01568G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01568G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01568G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01568G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01568G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01568G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01568G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01568G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01568G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01568G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01568G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01568G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01568G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01568G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01568G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01568G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01568G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01568G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01568G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01568G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01568G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01568G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01568G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
