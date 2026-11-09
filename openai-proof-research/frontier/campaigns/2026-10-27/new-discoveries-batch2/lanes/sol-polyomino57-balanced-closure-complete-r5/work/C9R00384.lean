import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R00384G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r384_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4)] := by
    let c9r384targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4),(3,4)]]
    let c9r384choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,5),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r384targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4)] c9r384choice = true := by decide
    refine ⟨c9r384targets, c9r384choice, ?_, checked⟩
    intro S h
    simp only [c9r384targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 16 _ (by rfl)
  have c9r385_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,2)] := by
    let c9r385targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,2),(4,2)]]
    let c9r385choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((3,1),(13,(0,0))),((3,3),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r385targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,2)] c9r385choice = true := by decide
    refine ⟨c9r385targets, c9r385choice, ?_, checked⟩
    intro S h
    simp only [c9r385targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 19 _ (by rfl)
  have c9r386_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,3)] := by
    let c9r386targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,3),(4,3)]]
    let c9r386choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,4),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r386targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,3)] c9r386choice = true := by decide
    refine ⟨c9r386targets, c9r386choice, ?_, checked⟩
    intro S h
    simp only [c9r386targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 21 _ (by rfl)
  have c9r387_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(2,5)] := by
    let c9r387targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(2,5),(3,5)]]
    let c9r387choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((2,6),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0))),((3,5),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r387targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(2,5)] c9r387choice = true := by decide
    refine ⟨c9r387targets, c9r387choice, ?_, checked⟩
    intro S h
    simp only [c9r387targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 25 _ (by rfl)
  have c9r388_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,3)] := by
    let c9r388targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,3),(4,3)]]
    let c9r388choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,5),(12,(0,0))),((3,2),(13,(0,0))),((3,4),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r388targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,3)] c9r388choice = true := by decide
    refine ⟨c9r388targets, c9r388choice, ?_, checked⟩
    intro S h
    simp only [c9r388targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 28 _ (by rfl)
  have c9r389_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,4)] := by
    let c9r389targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,4),(4,4)]]
    let c9r389choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,5),(12,(0,0))),((3,3),(13,(0,0))),((3,5),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r389targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,4)] c9r389choice = true := by decide
    refine ⟨c9r389targets, c9r389choice, ?_, checked⟩
    intro S h
    simp only [c9r389targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 30 _ (by rfl)
  have c9r390_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3)] := by
    let c9r390targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3),(4,3)]]
    let c9r390choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,1),(13,(0,0))),((3,4),(14,(0,0))),((4,2),(15,(0,0))),((4,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r390targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3)] c9r390choice = true := by decide
    refine ⟨c9r390targets, c9r390choice, ?_, checked⟩
    intro S h
    simp only [c9r390targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 2 _ (by rfl)
  have c9r391_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4)] := by
    let c9r391targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(4,4)]]
    let c9r391choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,5),(14,(0,0))),((4,3),(15,(0,0))),((4,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r391targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4)] c9r391choice = true := by decide
    refine ⟨c9r391targets, c9r391choice, ?_, checked⟩
    intro S h
    simp only [c9r391targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r384_closed
  · subst row; exact c9r385_closed
  · subst row; exact c9r386_closed
  · subst row; exact c9r387_closed
  · subst row; exact c9r388_closed
  · subst row; exact c9r389_closed
  · subst row; exact c9r390_closed
  · subst row; exact c9r391_closed
theorem C9R00384G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r392_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3)] := by
    let c9r392targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(4,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3),(5,3)]]
    let c9r392choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,4),(14,(0,0))),((4,2),(15,(0,0))),((4,4),(16,(0,0))),((5,3),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r392targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3)] c9r392choice = true := by decide
    refine ⟨c9r392targets, c9r392choice, ?_, checked⟩
    intro S h
    simp only [c9r392targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 8 _ (by rfl)
  have c9r393_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r393targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r393choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0))),((3,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r393targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3)] c9r393choice = true := by decide
    refine ⟨c9r393targets, c9r393choice, ?_, checked⟩
    intro S h
    simp only [c9r393targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 13 _ (by rfl)
  have c9r394_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0)] := by
    let c9r394targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c9r394choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,3),(11,(0,0))),((3,-1),(12,(0,1))),((3,1),(13,(0,0))),((3,2),(14,(0,0))),((4,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r394targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0)] c9r394choice = true := by decide
    refine ⟨c9r394targets, c9r394choice, ?_, checked⟩
    intro S h
    simp only [c9r394targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 16 _ (by rfl)
  have c9r395_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,1)] := by
    let c9r395targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c9r395choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,3),(11,(0,0))),((3,0),(12,(0,0))),((3,2),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r395targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,1)] c9r395choice = true := by decide
    refine ⟨c9r395targets, c9r395choice, ?_, checked⟩
    intro S h
    simp only [c9r395targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 18 _ (by rfl)
  have c9r396_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,2)] := by
    let c9r396targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c9r396choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,3),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0))),((3,3),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r396targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,2)] c9r396choice = true := by decide
    refine ⟨c9r396targets, c9r396choice, ?_, checked⟩
    intro S h
    simp only [c9r396targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 20 _ (by rfl)
  have c9r397_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1)] := by
    let c9r397targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c9r397choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((3,-1),(12,(0,1))),((3,2),(13,(0,0))),((4,0),(14,(0,0))),((4,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r397targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1)] c9r397choice = true := by decide
    refine ⟨c9r397targets, c9r397choice, ?_, checked⟩
    intro S h
    simp only [c9r397targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 23 _ (by rfl)
  have c9r398_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(4,0)] := by
    let c9r398targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c9r398choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((3,-1),(12,(0,1))),((3,1),(13,(0,0))),((4,-1),(14,(0,1))),((4,1),(15,(0,0))),((5,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r398targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(4,0)] c9r398choice = true := by decide
    refine ⟨c9r398targets, c9r398choice, ?_, checked⟩
    intro S h
    simp only [c9r398targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 25 _ (by rfl)
  have c9r399_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(3,2)] := by
    let c9r399targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c9r399choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((3,0),(12,(0,0))),((3,3),(13,(0,0))),((4,1),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r399targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(3,2)] c9r399choice = true := by decide
    refine ⟨c9r399targets, c9r399choice, ?_, checked⟩
    intro S h
    simp only [c9r399targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r392_closed
  · subst row; exact c9r393_closed
  · subst row; exact c9r394_closed
  · subst row; exact c9r395_closed
  · subst row; exact c9r396_closed
  · subst row; exact c9r397_closed
  · subst row; exact c9r398_closed
  · subst row; exact c9r399_closed
theorem C9R00384G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r400_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(4,1)] := by
    let c9r400targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c9r400choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((3,0),(12,(0,0))),((3,2),(13,(0,0))),((4,0),(14,(0,0))),((4,2),(15,(0,0))),((5,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r400targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(4,1)] c9r400choice = true := by decide
    refine ⟨c9r400targets, c9r400choice, ?_, checked⟩
    intro S h
    simp only [c9r400targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 31 _ (by rfl)
  have c9r401_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(3,2)] := by
    let c9r401targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2)]]
    let c9r401choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((3,-1),(13,(0,1))),((3,3),(14,(0,0))),((4,0),(15,(0,0))),((4,1),(16,(0,0))),((4,2),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r401targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(3,2)] c9r401choice = true := by decide
    refine ⟨c9r401targets, c9r401choice, ?_, checked⟩
    intro S h
    simp only [c9r401targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 4 _ (by rfl)
  have c9r402_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,0)] := by
    let c9r402targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)]]
    let c9r402choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((3,-1),(12,(0,1))),((3,2),(13,(0,0))),((4,-1),(14,(0,1))),((4,1),(15,(0,0))),((5,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r402targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,0)] c9r402choice = true := by decide
    refine ⟨c9r402targets, c9r402choice, ?_, checked⟩
    intro S h
    simp only [c9r402targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 6 _ (by rfl)
  have c9r403_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,1)] := by
    let c9r403targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1)]]
    let c9r403choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((3,-1),(12,(0,1))),((3,2),(13,(0,0))),((4,0),(14,(0,0))),((4,2),(15,(0,0))),((5,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r403targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,1)] c9r403choice = true := by decide
    refine ⟨c9r403targets, c9r403choice, ?_, checked⟩
    intro S h
    simp only [c9r403targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 8 _ (by rfl)
  have c9r404_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(4,1)] := by
    let c9r404targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1)]]
    let c9r404choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((3,-1),(12,(0,1))),((3,1),(13,(0,0))),((4,-1),(14,(0,1))),((4,2),(15,(0,0))),((5,0),(16,(0,0))),((5,1),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r404targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(4,1)] c9r404choice = true := by decide
    refine ⟨c9r404targets, c9r404choice, ?_, checked⟩
    intro S h
    simp only [c9r404targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 11 _ (by rfl)
  have c9r405_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(5,0)] := by
    let c9r405targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0)]]
    let c9r405choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((3,-1),(12,(0,1))),((3,1),(13,(0,0))),((4,-1),(14,(0,1))),((4,1),(15,(0,0))),((5,-1),(16,(0,1))),((5,1),(17,(0,0))),((6,0),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r405targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(5,0)] c9r405choice = true := by decide
    refine ⟨c9r405targets, c9r405choice, ?_, checked⟩
    intro S h
    simp only [c9r405targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 13 _ (by rfl)
  have c9r406_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c9r406targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c9r406choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,6),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r406targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)] c9r406choice = true := by decide
    refine ⟨c9r406targets, c9r406choice, ?_, checked⟩
    intro S h
    simp only [c9r406targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 19 _ (by rfl)
  have c9r407_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c9r407targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c9r407choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r407targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)] c9r407choice = true := by decide
    refine ⟨c9r407targets, c9r407choice, ?_, checked⟩
    intro S h
    simp only [c9r407targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r400_closed
  · subst row; exact c9r401_closed
  · subst row; exact c9r402_closed
  · subst row; exact c9r403_closed
  · subst row; exact c9r404_closed
  · subst row; exact c9r405_closed
  · subst row; exact c9r406_closed
  · subst row; exact c9r407_closed
theorem C9R00384G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r408_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c9r408targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c9r408choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r408targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)] c9r408choice = true := by decide
    refine ⟨c9r408targets, c9r408choice, ?_, checked⟩
    intro S h
    simp only [c9r408targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 27 _ (by rfl)
  have c9r409_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c9r409targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c9r409choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r409targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)] c9r409choice = true := by decide
    refine ⟨c9r409targets, c9r409choice, ?_, checked⟩
    intro S h
    simp only [c9r409targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 29 _ (by rfl)
  have c9r410_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c9r410targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c9r410choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r410targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)] c9r410choice = true := by decide
    refine ⟨c9r410targets, c9r410choice, ?_, checked⟩
    intro S h
    simp only [c9r410targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 31 _ (by rfl)
  have c9r411_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c9r411targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c9r411choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r411targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)] c9r411choice = true := by decide
    refine ⟨c9r411targets, c9r411choice, ?_, checked⟩
    intro S h
    simp only [c9r411targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 3 _ (by rfl)
  have c9r412_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)] := by
    let c9r412targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
    let c9r412choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r412targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)] c9r412choice = true := by decide
    refine ⟨c9r412targets, c9r412choice, ?_, checked⟩
    intro S h
    simp only [c9r412targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 6 _ (by rfl)
  have c9r413_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)] := by
    let c9r413targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
    let c9r413choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r413targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)] c9r413choice = true := by decide
    refine ⟨c9r413targets, c9r413choice, ?_, checked⟩
    intro S h
    simp only [c9r413targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 9 _ (by rfl)
  have c9r414_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)] := by
    let c9r414targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
    let c9r414choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r414targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)] c9r414choice = true := by decide
    refine ⟨c9r414targets, c9r414choice, ?_, checked⟩
    intro S h
    simp only [c9r414targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 12 _ (by rfl)
  have c9r415_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)] := by
    let c9r415targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
    let c9r415choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r415targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)] c9r415choice = true := by decide
    refine ⟨c9r415targets, c9r415choice, ?_, checked⟩
    intro S h
    simp only [c9r415targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,false,true,true,false,false] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r408_closed
  · subst row; exact c9r409_closed
  · subst row; exact c9r410_closed
  · subst row; exact c9r411_closed
  · subst row; exact c9r412_closed
  · subst row; exact c9r413_closed
  · subst row; exact c9r414_closed
  · subst row; exact c9r415_closed
theorem C9R00384_closed (row : List GridPoint) (h : FamilyMember row F9B000L12) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L12, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R00384G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00384G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00384G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00384G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00384G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00384G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00384G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00384G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00384G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00384G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00384G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00384G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00384G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00384G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00384G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00384G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00384G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00384G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00384G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00384G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00384G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00384G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00384G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00384G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00384G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00384G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00384G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00384G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00384G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00384G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00384G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00384G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
