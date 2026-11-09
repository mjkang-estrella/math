import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01504G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1504_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)] := by
    let c8r1504targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)]]
    let c8r1504choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1504targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)] c8r1504choice = true := by decide
    refine ⟨c8r1504targets, c8r1504choice, ?_, checked⟩
    intro S h
    simp only [c8r1504targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 1 _ (by rfl)
  have c8r1505_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)] := by
    let c8r1505targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)]]
    let c8r1505choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1505targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)] c8r1505choice = true := by decide
    refine ⟨c8r1505targets, c8r1505choice, ?_, checked⟩
    intro S h
    simp only [c8r1505targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 3 _ (by rfl)
  have c8r1506_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)] := by
    let c8r1506targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)]]
    let c8r1506choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1506targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)] c8r1506choice = true := by decide
    refine ⟨c8r1506targets, c8r1506choice, ?_, checked⟩
    intro S h
    simp only [c8r1506targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 7 _ (by rfl)
  have c8r1507_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)] := by
    let c8r1507targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)]]
    let c8r1507choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1507targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)] c8r1507choice = true := by decide
    refine ⟨c8r1507targets, c8r1507choice, ?_, checked⟩
    intro S h
    simp only [c8r1507targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 10 _ (by rfl)
  have c8r1508_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)] := by
    let c8r1508targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)]]
    let c8r1508choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1508targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)] c8r1508choice = true := by decide
    refine ⟨c8r1508targets, c8r1508choice, ?_, checked⟩
    intro S h
    simp only [c8r1508targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 13 _ (by rfl)
  have c8r1509_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)] := by
    let c8r1509targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)]]
    let c8r1509choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,6),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0))),((3,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1509targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)] c8r1509choice = true := by decide
    refine ⟨c8r1509targets, c8r1509choice, ?_, checked⟩
    intro S h
    simp only [c8r1509targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 17 _ (by rfl)
  have c8r1510_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)] := by
    let c8r1510targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)]]
    let c8r1510choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1510targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)] c8r1510choice = true := by decide
    refine ⟨c8r1510targets, c8r1510choice, ?_, checked⟩
    intro S h
    simp only [c8r1510targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 20 _ (by rfl)
  have c8r1511_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)] := by
    let c8r1511targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)]]
    let c8r1511choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,3),(10,(0,0))),((3,5),(11,(0,0))),((4,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1511targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)] c8r1511choice = true := by decide
    refine ⟨c8r1511targets, c8r1511choice, ?_, checked⟩
    intro S h
    simp only [c8r1511targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 22 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1504_closed
  · subst row; exact c8r1505_closed
  · subst row; exact c8r1506_closed
  · subst row; exact c8r1507_closed
  · subst row; exact c8r1508_closed
  · subst row; exact c8r1509_closed
  · subst row; exact c8r1510_closed
  · subst row; exact c8r1511_closed
theorem C8R01504G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1512_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)] := by
    let c8r1512targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)]]
    let c8r1512choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1512targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)] c8r1512choice = true := by decide
    refine ⟨c8r1512targets, c8r1512choice, ?_, checked⟩
    intro S h
    simp only [c8r1512targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 26 _ (by rfl)
  have c8r1513_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)] := by
    let c8r1513targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)]]
    let c8r1513choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,5),(11,(0,0))),((4,3),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1513targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)] c8r1513choice = true := by decide
    refine ⟨c8r1513targets, c8r1513choice, ?_, checked⟩
    intro S h
    simp only [c8r1513targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 29 _ (by rfl)
  have c8r1514_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)] := by
    let c8r1514targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)]]
    let c8r1514choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1514targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)] c8r1514choice = true := by decide
    refine ⟨c8r1514targets, c8r1514choice, ?_, checked⟩
    intro S h
    simp only [c8r1514targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 0 _ (by rfl)
  have c8r1515_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)] := by
    let c8r1515targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)]]
    let c8r1515choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,4),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1515targets [(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)] c8r1515choice = true := by decide
    refine ⟨c8r1515targets, c8r1515choice, ?_, checked⟩
    intro S h
    simp only [c8r1515targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 7 _ (by rfl)
  have c8r1516_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1516targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1516choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,4),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1516targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)] c8r1516choice = true := by decide
    refine ⟨c8r1516targets, c8r1516choice, ?_, checked⟩
    intro S h
    simp only [c8r1516targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 13 _ (by rfl)
  have c8r1517_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r1517targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r1517choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1517targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)] c8r1517choice = true := by decide
    refine ⟨c8r1517targets, c8r1517choice, ?_, checked⟩
    intro S h
    simp only [c8r1517targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 16 _ (by rfl)
  have c8r1518_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r1518targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r1518choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,1),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1518targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)] c8r1518choice = true := by decide
    refine ⟨c8r1518targets, c8r1518choice, ?_, checked⟩
    intro S h
    simp only [c8r1518targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 18 _ (by rfl)
  have c8r1519_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r1519targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r1519choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1519targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)] c8r1519choice = true := by decide
    refine ⟨c8r1519targets, c8r1519choice, ?_, checked⟩
    intro S h
    simp only [c8r1519targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1512_closed
  · subst row; exact c8r1513_closed
  · subst row; exact c8r1514_closed
  · subst row; exact c8r1515_closed
  · subst row; exact c8r1516_closed
  · subst row; exact c8r1517_closed
  · subst row; exact c8r1518_closed
  · subst row; exact c8r1519_closed
theorem C8R01504G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1520_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)] := by
    let c8r1520targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1520choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1520targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)] c8r1520choice = true := by decide
    refine ⟨c8r1520targets, c8r1520choice, ?_, checked⟩
    intro S h
    simp only [c8r1520targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 23 _ (by rfl)
  have c8r1521_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)] := by
    let c8r1521targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c8r1521choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1521targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)] c8r1521choice = true := by decide
    refine ⟨c8r1521targets, c8r1521choice, ?_, checked⟩
    intro S h
    simp only [c8r1521targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 25 _ (by rfl)
  have c8r1522_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)] := by
    let c8r1522targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c8r1522choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1522targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)] c8r1522choice = true := by decide
    refine ⟨c8r1522targets, c8r1522choice, ?_, checked⟩
    intro S h
    simp only [c8r1522targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 28 _ (by rfl)
  have c8r1523_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)] := by
    let c8r1523targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c8r1523choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1523targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)] c8r1523choice = true := by decide
    refine ⟨c8r1523targets, c8r1523choice, ?_, checked⟩
    intro S h
    simp only [c8r1523targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 31 _ (by rfl)
  have c8r1524_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)] := by
    let c8r1524targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)]]
    let c8r1524choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1524targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)] c8r1524choice = true := by decide
    refine ⟨c8r1524targets, c8r1524choice, ?_, checked⟩
    intro S h
    simp only [c8r1524targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 4 _ (by rfl)
  have c8r1525_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)] := by
    let c8r1525targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(4,0)]]
    let c8r1525choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1525targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)] c8r1525choice = true := by decide
    refine ⟨c8r1525targets, c8r1525choice, ?_, checked⟩
    intro S h
    simp only [c8r1525targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 8 _ (by rfl)
  have c8r1526_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)] := by
    let c8r1526targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2)]]
    let c8r1526choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1526targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)] c8r1526choice = true := by decide
    refine ⟨c8r1526targets, c8r1526choice, ?_, checked⟩
    intro S h
    simp only [c8r1526targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 11 _ (by rfl)
  have c8r1527_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)] := by
    let c8r1527targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3)]]
    let c8r1527choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1527targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)] c8r1527choice = true := by decide
    refine ⟨c8r1527targets, c8r1527choice, ?_, checked⟩
    intro S h
    simp only [c8r1527targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1520_closed
  · subst row; exact c8r1521_closed
  · subst row; exact c8r1522_closed
  · subst row; exact c8r1523_closed
  · subst row; exact c8r1524_closed
  · subst row; exact c8r1525_closed
  · subst row; exact c8r1526_closed
  · subst row; exact c8r1527_closed
theorem C8R01504G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1528_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)] := by
    let c8r1528targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,1)]]
    let c8r1528choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1528targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)] c8r1528choice = true := by decide
    refine ⟨c8r1528targets, c8r1528choice, ?_, checked⟩
    intro S h
    simp only [c8r1528targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 16 _ (by rfl)
  have c8r1529_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)] := by
    let c8r1529targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,2)]]
    let c8r1529choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1529targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)] c8r1529choice = true := by decide
    refine ⟨c8r1529targets, c8r1529choice, ?_, checked⟩
    intro S h
    simp only [c8r1529targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 19 _ (by rfl)
  have c8r1530_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)] := by
    let c8r1530targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0)]]
    let c8r1530choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1530targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)] c8r1530choice = true := by decide
    refine ⟨c8r1530targets, c8r1530choice, ?_, checked⟩
    intro S h
    simp only [c8r1530targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 21 _ (by rfl)
  have c8r1531_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)] := by
    let c8r1531targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2)]]
    let c8r1531choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1531targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)] c8r1531choice = true := by decide
    refine ⟨c8r1531targets, c8r1531choice, ?_, checked⟩
    intro S h
    simp only [c8r1531targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 24 _ (by rfl)
  have c8r1532_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)] := by
    let c8r1532targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3)]]
    let c8r1532choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1532targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)] c8r1532choice = true := by decide
    refine ⟨c8r1532targets, c8r1532choice, ?_, checked⟩
    intro S h
    simp only [c8r1532targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 27 _ (by rfl)
  have c8r1533_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)] := by
    let c8r1533targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2)]]
    let c8r1533choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1533targets [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)] c8r1533choice = true := by decide
    refine ⟨c8r1533targets, c8r1533choice, ?_, checked⟩
    intro S h
    simp only [c8r1533targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 30 _ (by rfl)
  have c8r1534_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)] := by
    let c8r1534targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1534choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1534targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)] c8r1534choice = true := by decide
    refine ⟨c8r1534targets, c8r1534choice, ?_, checked⟩
    intro S h
    simp only [c8r1534targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,true] 2 _ (by rfl)
  have c8r1535_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)] := by
    let c8r1535targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)]]
    let c8r1535choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1535targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)] c8r1535choice = true := by decide
    refine ⟨c8r1535targets, c8r1535choice, ?_, checked⟩
    intro S h
    simp only [c8r1535targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,true] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1528_closed
  · subst row; exact c8r1529_closed
  · subst row; exact c8r1530_closed
  · subst row; exact c8r1531_closed
  · subst row; exact c8r1532_closed
  · subst row; exact c8r1533_closed
  · subst row; exact c8r1534_closed
  · subst row; exact c8r1535_closed
theorem C8R01504_closed (row : List GridPoint) (h : FamilyMember row F8B000L47) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L47, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01504G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01504G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01504G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01504G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01504G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01504G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01504G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01504G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01504G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01504G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01504G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01504G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01504G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01504G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01504G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01504G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01504G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01504G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01504G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01504G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01504G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01504G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01504G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01504G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01504G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01504G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01504G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01504G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01504G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01504G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01504G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01504G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
