import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00704G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r704_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)] := by
    let c8r704targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
    let c8r704choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r704targets [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)] c8r704choice = true := by decide
    refine ⟨c8r704targets, c8r704choice, ?_, checked⟩
    intro S h
    simp only [c8r704targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 0 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 5 _ (by rfl)))
  have c8r705_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)] := by
    let c8r705targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
    let c8r705choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r705targets [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)] c8r705choice = true := by decide
    refine ⟨c8r705targets, c8r705choice, ?_, checked⟩
    intro S h
    simp only [c8r705targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 1 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 8 _ (by rfl)))
  have c8r706_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)] := by
    let c8r706targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
    let c8r706choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r706targets [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)] c8r706choice = true := by decide
    refine ⟨c8r706targets, c8r706choice, ?_, checked⟩
    intro S h
    simp only [c8r706targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 2 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 10 _ (by rfl)))
  have c8r707_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)] := by
    let c8r707targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
    let c8r707choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r707targets [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)] c8r707choice = true := by decide
    refine ⟨c8r707targets, c8r707choice, ?_, checked⟩
    intro S h
    simp only [c8r707targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 3 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 12 _ (by rfl)))
  have c8r708_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)] := by
    let c8r708targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]]
    let c8r708choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r708targets [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)] c8r708choice = true := by decide
    refine ⟨c8r708targets, c8r708choice, ?_, checked⟩
    intro S h
    simp only [c8r708targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 4 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 15 _ (by rfl)))
  have c8r709_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)] := by
    let c8r709targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]]
    let c8r709choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r709targets [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)] c8r709choice = true := by decide
    refine ⟨c8r709targets, c8r709choice, ?_, checked⟩
    intro S h
    simp only [c8r709targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 5 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 18 _ (by rfl)))
  have c8r710_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)] := by
    let c8r710targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]]
    let c8r710choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r710targets [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)] c8r710choice = true := by decide
    refine ⟨c8r710targets, c8r710choice, ?_, checked⟩
    intro S h
    simp only [c8r710targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 6 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 20 _ (by rfl)))
  have c8r711_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)] := by
    let c8r711targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]]
    let c8r711choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r711targets [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)] c8r711choice = true := by decide
    refine ⟨c8r711targets, c8r711choice, ?_, checked⟩
    intro S h
    simp only [c8r711targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 7 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 23 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r704_closed
  · subst row; exact c8r705_closed
  · subst row; exact c8r706_closed
  · subst row; exact c8r707_closed
  · subst row; exact c8r708_closed
  · subst row; exact c8r709_closed
  · subst row; exact c8r710_closed
  · subst row; exact c8r711_closed
theorem C8R00704G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r712_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)] := by
    let c8r712targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]]
    let c8r712choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r712targets [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)] c8r712choice = true := by decide
    refine ⟨c8r712targets, c8r712choice, ?_, checked⟩
    intro S h
    simp only [c8r712targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 8 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 26 _ (by rfl)))
  have c8r713_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)] := by
    let c8r713targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]]
    let c8r713choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r713targets [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)] c8r713choice = true := by decide
    refine ⟨c8r713targets, c8r713choice, ?_, checked⟩
    intro S h
    simp only [c8r713targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 9 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 29 _ (by rfl)))
  have c8r714_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)] := by
    let c8r714targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]]
    let c8r714choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r714targets [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)] c8r714choice = true := by decide
    refine ⟨c8r714targets, c8r714choice, ?_, checked⟩
    intro S h
    simp only [c8r714targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 10 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 0 _ (by rfl)))
  have c8r715_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)] := by
    let c8r715targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)]]
    let c8r715choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r715targets [(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)] c8r715choice = true := by decide
    refine ⟨c8r715targets, c8r715choice, ?_, checked⟩
    intro S h
    simp only [c8r715targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 11 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 6 _ (by rfl)))
  have c8r716_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r716targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,3),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r716choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r716targets [(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)] c8r716choice = true := by decide
    refine ⟨c8r716targets, c8r716choice, ?_, checked⟩
    intro S h
    simp only [c8r716targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 12 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 14 _ (by rfl)))
  have c8r717_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r717targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r717choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r717targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r717choice = true := by decide
    refine ⟨c8r717targets, c8r717choice, ?_, checked⟩
    intro S h
    simp only [c8r717targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 22 _ (by rfl)))
  have c8r718_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] := by
    let c8r718targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
    let c8r718choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r718targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] c8r718choice = true := by decide
    refine ⟨c8r718targets, c8r718choice, ?_, checked⟩
    intro S h
    simp only [c8r718targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 27 _ (by rfl)))
  have c8r719_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c8r719targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c8r719choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r719targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] c8r719choice = true := by decide
    refine ⟨c8r719targets, c8r719choice, ?_, checked⟩
    intro S h
    simp only [c8r719targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 31 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r712_closed
  · subst row; exact c8r713_closed
  · subst row; exact c8r714_closed
  · subst row; exact c8r715_closed
  · subst row; exact c8r716_closed
  · subst row; exact c8r717_closed
  · subst row; exact c8r718_closed
  · subst row; exact c8r719_closed
theorem C8R00704G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r720_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c8r720targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c8r720choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r720targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] c8r720choice = true := by decide
    refine ⟨c8r720targets, c8r720choice, ?_, checked⟩
    intro S h
    simp only [c8r720targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 2 _ (by rfl)))
  have c8r721_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c8r721targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c8r721choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r721targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] c8r721choice = true := by decide
    refine ⟨c8r721targets, c8r721choice, ?_, checked⟩
    intro S h
    simp only [c8r721targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 4 _ (by rfl)))
  have c8r722_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r722targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r722choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r722targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] c8r722choice = true := by decide
    refine ⟨c8r722targets, c8r722choice, ?_, checked⟩
    intro S h
    simp only [c8r722targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 6 _ (by rfl)))
  have c8r723_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c8r723targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c8r723choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r723targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] c8r723choice = true := by decide
    refine ⟨c8r723targets, c8r723choice, ?_, checked⟩
    intro S h
    simp only [c8r723targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L22_lift _ (familyLookup_sound F9B002L22 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 10 _ (by rfl)))
  have c8r724_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] := by
    let c8r724targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)]]
    let c8r724choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r724targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] c8r724choice = true := by decide
    refine ⟨c8r724targets, c8r724choice, ?_, checked⟩
    intro S h
    simp only [c8r724targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 13 _ (by rfl)))
  have c8r725_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] := by
    let c8r725targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)]]
    let c8r725choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r725targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] c8r725choice = true := by decide
    refine ⟨c8r725targets, c8r725choice, ?_, checked⟩
    intro S h
    simp only [c8r725targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 16 _ (by rfl)))
  have c8r726_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] := by
    let c8r726targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)]]
    let c8r726choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r726targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] c8r726choice = true := by decide
    refine ⟨c8r726targets, c8r726choice, ?_, checked⟩
    intro S h
    simp only [c8r726targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 18 _ (by rfl)))
  have c8r727_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] := by
    let c8r727targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
    let c8r727choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r727targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] c8r727choice = true := by decide
    refine ⟨c8r727targets, c8r727choice, ?_, checked⟩
    intro S h
    simp only [c8r727targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 21 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r720_closed
  · subst row; exact c8r721_closed
  · subst row; exact c8r722_closed
  · subst row; exact c8r723_closed
  · subst row; exact c8r724_closed
  · subst row; exact c8r725_closed
  · subst row; exact c8r726_closed
  · subst row; exact c8r727_closed
theorem C8R00704G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r728_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] := by
    let c8r728targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
    let c8r728choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r728targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] c8r728choice = true := by decide
    refine ⟨c8r728targets, c8r728choice, ?_, checked⟩
    intro S h
    simp only [c8r728targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 24 _ (by rfl)))
  have c8r729_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] := by
    let c8r729targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
    let c8r729choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r729targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] c8r729choice = true := by decide
    refine ⟨c8r729targets, c8r729choice, ?_, checked⟩
    intro S h
    simp only [c8r729targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 27 _ (by rfl)))
  have c8r730_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] := by
    let c8r730targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
    let c8r730choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r730targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] c8r730choice = true := by decide
    refine ⟨c8r730targets, c8r730choice, ?_, checked⟩
    intro S h
    simp only [c8r730targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 30 _ (by rfl)))
  have c8r731_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] := by
    let c8r731targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
    let c8r731choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r731targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] c8r731choice = true := by decide
    refine ⟨c8r731targets, c8r731choice, ?_, checked⟩
    intro S h
    simp only [c8r731targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 1 _ (by rfl)))
  have c8r732_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)] := by
    let c8r732targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
    let c8r732choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r732targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)] c8r732choice = true := by decide
    refine ⟨c8r732targets, c8r732choice, ?_, checked⟩
    intro S h
    simp only [c8r732targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 4 _ (by rfl)))
  have c8r733_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)] := by
    let c8r733targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
    let c8r733choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r733targets [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)] c8r733choice = true := by decide
    refine ⟨c8r733targets, c8r733choice, ?_, checked⟩
    intro S h
    simp only [c8r733targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 7 _ (by rfl)))
  have c8r734_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)] := by
    let c8r734targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]
    let c8r734choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r734targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)] c8r734choice = true := by decide
    refine ⟨c8r734targets, c8r734choice, ?_, checked⟩
    intro S h
    simp only [c8r734targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 12 _ (by rfl)))
  have c8r735_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)] := by
    let c8r735targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]
    let c8r735choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r735targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)] c8r735choice = true := by decide
    refine ⟨c8r735targets, c8r735choice, ?_, checked⟩
    intro S h
    simp only [c8r735targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L41_lift _ (familyLookup_sound F9B003L41 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 14 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r728_closed
  · subst row; exact c8r729_closed
  · subst row; exact c8r730_closed
  · subst row; exact c8r731_closed
  · subst row; exact c8r732_closed
  · subst row; exact c8r733_closed
  · subst row; exact c8r734_closed
  · subst row; exact c8r735_closed
theorem C8R00704_closed (row : List GridPoint) (h : FamilyMember row F8B000L22) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L22, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00704G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00704G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00704G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00704G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00704G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00704G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00704G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00704G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00704G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00704G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00704G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00704G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00704G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00704G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00704G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00704G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00704G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00704G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00704G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00704G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00704G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00704G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00704G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00704G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00704G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00704G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00704G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00704G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00704G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00704G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00704G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00704G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
