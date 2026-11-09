import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01408G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1408_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)] := by
    let c8r1408targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
    let c8r1408choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1408targets [(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)] c8r1408choice = true := by decide
    refine ⟨c8r1408targets, c8r1408choice, ?_, checked⟩
    intro S h
    simp only [c8r1408targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 8 _ (by rfl)
  have c8r1409_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c8r1409targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c8r1409choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1409targets [(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)] c8r1409choice = true := by decide
    refine ⟨c8r1409targets, c8r1409choice, ?_, checked⟩
    intro S h
    simp only [c8r1409targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 10 _ (by rfl)
  have c8r1410_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c8r1410targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c8r1410choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1410targets [(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)] c8r1410choice = true := by decide
    refine ⟨c8r1410targets, c8r1410choice, ?_, checked⟩
    intro S h
    simp only [c8r1410targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 14 _ (by rfl)
  have c8r1411_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c8r1411targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1411choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1411targets [(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)] c8r1411choice = true := by decide
    refine ⟨c8r1411targets, c8r1411choice, ?_, checked⟩
    intro S h
    simp only [c8r1411targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 21 _ (by rfl)
  have c8r1412_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r1412targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r1412choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1412targets [(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)] c8r1412choice = true := by decide
    refine ⟨c8r1412targets, c8r1412choice, ?_, checked⟩
    intro S h
    simp only [c8r1412targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 28 _ (by rfl)
  have c8r1413_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r1413targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r1413choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1413targets [(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)] c8r1413choice = true := by decide
    refine ⟨c8r1413targets, c8r1413choice, ?_, checked⟩
    intro S h
    simp only [c8r1413targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 31 _ (by rfl)
  have c8r1414_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r1414targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r1414choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1414targets [(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)] c8r1414choice = true := by decide
    refine ⟨c8r1414targets, c8r1414choice, ?_, checked⟩
    intro S h
    simp only [c8r1414targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 1 _ (by rfl)
  have c8r1415_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c8r1415targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c8r1415choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1415targets [(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)] c8r1415choice = true := by decide
    refine ⟨c8r1415targets, c8r1415choice, ?_, checked⟩
    intro S h
    simp only [c8r1415targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 3 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1408_closed
  · subst row; exact c8r1409_closed
  · subst row; exact c8r1410_closed
  · subst row; exact c8r1411_closed
  · subst row; exact c8r1412_closed
  · subst row; exact c8r1413_closed
  · subst row; exact c8r1414_closed
  · subst row; exact c8r1415_closed
theorem C8R01408G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1416_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)] := by
    let c8r1416targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c8r1416choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1416targets [(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)] c8r1416choice = true := by decide
    refine ⟨c8r1416targets, c8r1416choice, ?_, checked⟩
    intro S h
    simp only [c8r1416targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 8 _ (by rfl)
  have c8r1417_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)] := by
    let c8r1417targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c8r1417choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,3),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1417targets [(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)] c8r1417choice = true := by decide
    refine ⟨c8r1417targets, c8r1417choice, ?_, checked⟩
    intro S h
    simp only [c8r1417targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 14 _ (by rfl)
  have c8r1418_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)] := by
    let c8r1418targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,5),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3)],[(0,2),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3)]]
    let c8r1418choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((-1,5),(3,(1,0))),((0,0),(4,(0,0))),((0,2),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,4),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1418targets [(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)] c8r1418choice = true := by decide
    refine ⟨c8r1418targets, c8r1418choice, ?_, checked⟩
    intro S h
    simp only [c8r1418targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 23 _ (by rfl)
  have c8r1419_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r1419targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r1419choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,2),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1419targets [(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)] c8r1419choice = true := by decide
    refine ⟨c8r1419targets, c8r1419choice, ?_, checked⟩
    intro S h
    simp only [c8r1419targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 30 _ (by rfl)
  have c8r1420_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)] := by
    let c8r1420targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
    let c8r1420choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,2),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1420targets [(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)] c8r1420choice = true := by decide
    refine ⟨c8r1420targets, c8r1420choice, ?_, checked⟩
    intro S h
    simp only [c8r1420targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 2 _ (by rfl)
  have c8r1421_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)] := by
    let c8r1421targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
    let c8r1421choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,2),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1421targets [(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)] c8r1421choice = true := by decide
    refine ⟨c8r1421targets, c8r1421choice, ?_, checked⟩
    intro S h
    simp only [c8r1421targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 5 _ (by rfl)
  have c8r1422_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)] := by
    let c8r1422targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
    let c8r1422choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,2),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1422targets [(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)] c8r1422choice = true := by decide
    refine ⟨c8r1422targets, c8r1422choice, ?_, checked⟩
    intro S h
    simp only [c8r1422targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 7 _ (by rfl)
  have c8r1423_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)] := by
    let c8r1423targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
    let c8r1423choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,2),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1423targets [(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)] c8r1423choice = true := by decide
    refine ⟨c8r1423targets, c8r1423choice, ?_, checked⟩
    intro S h
    simp only [c8r1423targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1416_closed
  · subst row; exact c8r1417_closed
  · subst row; exact c8r1418_closed
  · subst row; exact c8r1419_closed
  · subst row; exact c8r1420_closed
  · subst row; exact c8r1421_closed
  · subst row; exact c8r1422_closed
  · subst row; exact c8r1423_closed
theorem C8R01408G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1424_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c8r1424targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,4),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c8r1424choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,2),(4,(0,0))),((0,5),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1424targets [(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)] c8r1424choice = true := by decide
    refine ⟨c8r1424targets, c8r1424choice, ?_, checked⟩
    intro S h
    simp only [c8r1424targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 15 _ (by rfl)
  have c8r1425_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r1425targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r1425choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,6),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1425targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r1425choice = true := by decide
    refine ⟨c8r1425targets, c8r1425choice, ?_, checked⟩
    intro S h
    simp only [c8r1425targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 25 _ (by rfl)
  have c8r1426_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] := by
    let c8r1426targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
    let c8r1426choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1426targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] c8r1426choice = true := by decide
    refine ⟨c8r1426targets, c8r1426choice, ?_, checked⟩
    intro S h
    simp only [c8r1426targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 30 _ (by rfl)
  have c8r1427_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c8r1427targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c8r1427choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1427targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] c8r1427choice = true := by decide
    refine ⟨c8r1427targets, c8r1427choice, ?_, checked⟩
    intro S h
    simp only [c8r1427targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 2 _ (by rfl)
  have c8r1428_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c8r1428targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c8r1428choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1428targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] c8r1428choice = true := by decide
    refine ⟨c8r1428targets, c8r1428choice, ?_, checked⟩
    intro S h
    simp only [c8r1428targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 5 _ (by rfl)
  have c8r1429_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c8r1429targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c8r1429choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1429targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] c8r1429choice = true := by decide
    refine ⟨c8r1429targets, c8r1429choice, ?_, checked⟩
    intro S h
    simp only [c8r1429targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 7 _ (by rfl)
  have c8r1430_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r1430targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r1430choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1430targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] c8r1430choice = true := by decide
    refine ⟨c8r1430targets, c8r1430choice, ?_, checked⟩
    intro S h
    simp only [c8r1430targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 9 _ (by rfl)
  have c8r1431_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c8r1431targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c8r1431choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1431targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] c8r1431choice = true := by decide
    refine ⟨c8r1431targets, c8r1431choice, ?_, checked⟩
    intro S h
    simp only [c8r1431targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1424_closed
  · subst row; exact c8r1425_closed
  · subst row; exact c8r1426_closed
  · subst row; exact c8r1427_closed
  · subst row; exact c8r1428_closed
  · subst row; exact c8r1429_closed
  · subst row; exact c8r1430_closed
  · subst row; exact c8r1431_closed
theorem C8R01408G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1432_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] := by
    let c8r1432targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)]]
    let c8r1432choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1432targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] c8r1432choice = true := by decide
    refine ⟨c8r1432targets, c8r1432choice, ?_, checked⟩
    intro S h
    simp only [c8r1432targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 16 _ (by rfl)
  have c8r1433_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] := by
    let c8r1433targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)]]
    let c8r1433choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1433targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] c8r1433choice = true := by decide
    refine ⟨c8r1433targets, c8r1433choice, ?_, checked⟩
    intro S h
    simp only [c8r1433targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 19 _ (by rfl)
  have c8r1434_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] := by
    let c8r1434targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)]]
    let c8r1434choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1434targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] c8r1434choice = true := by decide
    refine ⟨c8r1434targets, c8r1434choice, ?_, checked⟩
    intro S h
    simp only [c8r1434targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 21 _ (by rfl)
  have c8r1435_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] := by
    let c8r1435targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
    let c8r1435choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1435targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] c8r1435choice = true := by decide
    refine ⟨c8r1435targets, c8r1435choice, ?_, checked⟩
    intro S h
    simp only [c8r1435targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 24 _ (by rfl)
  have c8r1436_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] := by
    let c8r1436targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
    let c8r1436choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1436targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] c8r1436choice = true := by decide
    refine ⟨c8r1436targets, c8r1436choice, ?_, checked⟩
    intro S h
    simp only [c8r1436targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 27 _ (by rfl)
  have c8r1437_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] := by
    let c8r1437targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
    let c8r1437choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1437targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] c8r1437choice = true := by decide
    refine ⟨c8r1437targets, c8r1437choice, ?_, checked⟩
    intro S h
    simp only [c8r1437targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 30 _ (by rfl)
  have c8r1438_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] := by
    let c8r1438targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
    let c8r1438choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1438targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] c8r1438choice = true := by decide
    refine ⟨c8r1438targets, c8r1438choice, ?_, checked⟩
    intro S h
    simp only [c8r1438targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 1 _ (by rfl)
  have c8r1439_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] := by
    let c8r1439targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
    let c8r1439choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1439targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] c8r1439choice = true := by decide
    refine ⟨c8r1439targets, c8r1439choice, ?_, checked⟩
    intro S h
    simp only [c8r1439targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1432_closed
  · subst row; exact c8r1433_closed
  · subst row; exact c8r1434_closed
  · subst row; exact c8r1435_closed
  · subst row; exact c8r1436_closed
  · subst row; exact c8r1437_closed
  · subst row; exact c8r1438_closed
  · subst row; exact c8r1439_closed
theorem C8R01408_closed (row : List GridPoint) (h : FamilyMember row F8B000L44) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L44, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01408G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01408G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01408G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01408G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01408G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01408G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01408G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01408G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01408G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01408G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01408G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01408G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01408G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01408G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01408G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01408G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01408G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01408G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01408G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01408G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01408G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01408G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01408G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01408G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01408G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01408G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01408G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01408G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01408G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01408G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01408G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01408G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
