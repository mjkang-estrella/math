import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01152G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1152_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)] := by
    let c8r1152targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,1)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(3,1)]]
    let c8r1152choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((-1,5),(4,(1,0))),((0,0),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((1,5),(11,(0,0))),((2,0),(12,(0,0))),((2,2),(13,(0,0))),((3,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1152targets [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)] c8r1152choice = true := by decide
    refine ⟨c8r1152targets, c8r1152choice, ?_, checked⟩
    intro S h
    simp only [c8r1152targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 29 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 26 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 22 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 2 _ (by rfl)))
  have c8r1153_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1)] := by
    let c8r1153targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(3,1)]]
    let c8r1153choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((-1,5),(4,(1,0))),((0,0),(5,(0,0))),((0,6),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((1,5),(11,(0,0))),((2,-1),(12,(0,1))),((2,2),(13,(0,0))),((3,0),(14,(0,0))),((3,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1153targets [(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1)] c8r1153choice = true := by decide
    refine ⟨c8r1153targets, c8r1153choice, ?_, checked⟩
    intro S h
    simp only [c8r1153targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 30 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 27 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 23 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 9 _ (by rfl)))
  have c8r1154_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)] := by
    let c8r1154targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)]]
    let c8r1154choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1154targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)] c8r1154choice = true := by decide
    refine ⟨c8r1154targets, c8r1154choice, ?_, checked⟩
    intro S h
    simp only [c8r1154targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 31 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 28 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 16 _ (by rfl)))
  have c8r1155_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)] := by
    let c8r1155targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4)]]
    let c8r1155choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1155targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)] c8r1155choice = true := by decide
    refine ⟨c8r1155targets, c8r1155choice, ?_, checked⟩
    intro S h
    simp only [c8r1155targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 0 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 29 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 21 _ (by rfl)))
  have c8r1156_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)] := by
    let c8r1156targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0)]]
    let c8r1156choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1156targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)] c8r1156choice = true := by decide
    refine ⟨c8r1156targets, c8r1156choice, ?_, checked⟩
    intro S h
    simp only [c8r1156targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 1 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 30 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 24 _ (by rfl)))
  have c8r1157_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)] := by
    let c8r1157targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1)]]
    let c8r1157choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1157targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)] c8r1157choice = true := by decide
    refine ⟨c8r1157targets, c8r1157choice, ?_, checked⟩
    intro S h
    simp only [c8r1157targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 2 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 31 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 26 _ (by rfl)))
  have c8r1158_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)] := by
    let c8r1158targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2)]]
    let c8r1158choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1158targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)] c8r1158choice = true := by decide
    refine ⟨c8r1158targets, c8r1158choice, ?_, checked⟩
    intro S h
    simp only [c8r1158targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 3 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 0 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 28 _ (by rfl)))
  have c8r1159_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)] := by
    let c8r1159targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4)]]
    let c8r1159choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1159targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)] c8r1159choice = true := by decide
    refine ⟨c8r1159targets, c8r1159choice, ?_, checked⟩
    intro S h
    simp only [c8r1159targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 4 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 1 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 1 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1152_closed
  · subst row; exact c8r1153_closed
  · subst row; exact c8r1154_closed
  · subst row; exact c8r1155_closed
  · subst row; exact c8r1156_closed
  · subst row; exact c8r1157_closed
  · subst row; exact c8r1158_closed
  · subst row; exact c8r1159_closed
theorem C8R01152G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1160_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0)] := by
    let c8r1160targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(3,0)]]
    let c8r1160choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1160targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0)] c8r1160choice = true := by decide
    refine ⟨c8r1160targets, c8r1160choice, ?_, checked⟩
    intro S h
    simp only [c8r1160targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 5 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 2 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 4 _ (by rfl)))
  have c8r1161_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1)] := by
    let c8r1161targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,1)]]
    let c8r1161choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1161targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1)] c8r1161choice = true := by decide
    refine ⟨c8r1161targets, c8r1161choice, ?_, checked⟩
    intro S h
    simp only [c8r1161targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 6 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 3 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 7 _ (by rfl)))
  have c8r1162_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3)] := by
    let c8r1162targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,3)]]
    let c8r1162choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1162targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3)] c8r1162choice = true := by decide
    refine ⟨c8r1162targets, c8r1162choice, ?_, checked⟩
    intro S h
    simp only [c8r1162targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 7 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 4 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 10 _ (by rfl)))
  have c8r1163_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5)] := by
    let c8r1163targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(1,6)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,5)]]
    let c8r1163choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,6),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1163targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5)] c8r1163choice = true := by decide
    refine ⟨c8r1163targets, c8r1163choice, ?_, checked⟩
    intro S h
    simp only [c8r1163targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 8 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 5 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 15 _ (by rfl)))
  have c8r1164_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0)] := by
    let c8r1164targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(3,0)]]
    let c8r1164choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,5),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((3,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1164targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0)] c8r1164choice = true := by decide
    refine ⟨c8r1164targets, c8r1164choice, ?_, checked⟩
    intro S h
    simp only [c8r1164targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 9 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 6 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 18 _ (by rfl)))
  have c8r1165_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1)] := by
    let c8r1165targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,1)]]
    let c8r1165choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1165targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1)] c8r1165choice = true := by decide
    refine ⟨c8r1165targets, c8r1165choice, ?_, checked⟩
    intro S h
    simp only [c8r1165targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 10 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 7 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 21 _ (by rfl)))
  have c8r1166_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4)] := by
    let c8r1166targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(2,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,4)]]
    let c8r1166choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1166targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4)] c8r1166choice = true := by decide
    refine ⟨c8r1166targets, c8r1166choice, ?_, checked⟩
    intro S h
    simp only [c8r1166targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 11 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 8 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 24 _ (by rfl)))
  have c8r1167_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)] := by
    let c8r1167targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1)]]
    let c8r1167choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1167targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)] c8r1167choice = true := by decide
    refine ⟨c8r1167targets, c8r1167choice, ?_, checked⟩
    intro S h
    simp only [c8r1167targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 12 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 9 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 27 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1160_closed
  · subst row; exact c8r1161_closed
  · subst row; exact c8r1162_closed
  · subst row; exact c8r1163_closed
  · subst row; exact c8r1164_closed
  · subst row; exact c8r1165_closed
  · subst row; exact c8r1166_closed
  · subst row; exact c8r1167_closed
theorem C8R01152G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1168_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0)] := by
    let c8r1168targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(3,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(3,0)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(4,0)]]
    let c8r1168choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((3,-1),(12,(0,1))),((3,1),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1168targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0)] c8r1168choice = true := by decide
    refine ⟨c8r1168targets, c8r1168choice, ?_, checked⟩
    intro S h
    simp only [c8r1168targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 13 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 10 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 29 _ (by rfl)))
  have c8r1169_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2)] := by
    let c8r1169targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,2)]]
    let c8r1169choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,3),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1169targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2)] c8r1169choice = true := by decide
    refine ⟨c8r1169targets, c8r1169choice, ?_, checked⟩
    intro S h
    simp only [c8r1169targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 14 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 11 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 0 _ (by rfl)))
  have c8r1170_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1)] := by
    let c8r1170targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(4,1)]]
    let c8r1170choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((3,0),(12,(0,0))),((3,2),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1170targets [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1)] c8r1170choice = true := by decide
    refine ⟨c8r1170targets, c8r1170choice, ?_, checked⟩
    intro S h
    simp only [c8r1170targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 15 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 12 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 3 _ (by rfl)))
  have c8r1171_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)] := by
    let c8r1171targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1)]]
    let c8r1171choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,0),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,2),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1171targets [(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)] c8r1171choice = true := by decide
    refine ⟨c8r1171targets, c8r1171choice, ?_, checked⟩
    intro S h
    simp only [c8r1171targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 16 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 13 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 9 _ (by rfl)))
  have c8r1172_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1)] := by
    let c8r1172targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(3,1)]]
    let c8r1172choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1172targets [(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1)] c8r1172choice = true := by decide
    refine ⟨c8r1172targets, c8r1172choice, ?_, checked⟩
    intro S h
    simp only [c8r1172targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 17 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 14 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 15 _ (by rfl)))
  have c8r1173_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1)] := by
    let c8r1173targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(3,1)]]
    let c8r1173choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,5),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,0),(13,(0,0))),((3,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1173targets [(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1)] c8r1173choice = true := by decide
    refine ⟨c8r1173targets, c8r1173choice, ?_, checked⟩
    intro S h
    simp only [c8r1173targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 18 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 15 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 21 _ (by rfl)))
  have c8r1174_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)] := by
    let c8r1174targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1174choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,3),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1174targets [(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)] c8r1174choice = true := by decide
    refine ⟨c8r1174targets, c8r1174choice, ?_, checked⟩
    intro S h
    simp only [c8r1174targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 19 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 16 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 26 _ (by rfl)))
  have c8r1175_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0)] := by
    let c8r1175targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(4,0)]]
    let c8r1175choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((3,-1),(12,(0,1))),((3,1),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1175targets [(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0)] c8r1175choice = true := by decide
    refine ⟨c8r1175targets, c8r1175choice, ?_, checked⟩
    intro S h
    simp only [c8r1175targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 20 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 17 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 28 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1168_closed
  · subst row; exact c8r1169_closed
  · subst row; exact c8r1170_closed
  · subst row; exact c8r1171_closed
  · subst row; exact c8r1172_closed
  · subst row; exact c8r1173_closed
  · subst row; exact c8r1174_closed
  · subst row; exact c8r1175_closed
theorem C8R01152G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1176_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)] := by
    let c8r1176targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(4,1)]]
    let c8r1176choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((3,0),(12,(0,0))),((3,2),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1176targets [(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)] c8r1176choice = true := by decide
    refine ⟨c8r1176targets, c8r1176choice, ?_, checked⟩
    intro S h
    simp only [c8r1176targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 21 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 18 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 30 _ (by rfl)))
  have c8r1177_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1)] := by
    let c8r1177targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1177choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((3,-1),(12,(0,1))),((3,2),(13,(0,0))),((4,0),(14,(0,0))),((4,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1177targets [(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1)] c8r1177choice = true := by decide
    refine ⟨c8r1177targets, c8r1177choice, ?_, checked⟩
    intro S h
    simp only [c8r1177targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 22 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 19 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 2 _ (by rfl)))
  have c8r1178_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)] := by
    let c8r1178targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1178choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,3),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1178targets [(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)] c8r1178choice = true := by decide
    refine ⟨c8r1178targets, c8r1178choice, ?_, checked⟩
    intro S h
    simp only [c8r1178targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 23 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 20 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 9 _ (by rfl)))
  have c8r1179_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r1179targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r1179choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1179targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)] c8r1179choice = true := by decide
    refine ⟨c8r1179targets, c8r1179choice, ?_, checked⟩
    intro S h
    simp only [c8r1179targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 24 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 19 _ (by rfl)))
  have c8r1180_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)] := by
    let c8r1180targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
    let c8r1180choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1180targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)] c8r1180choice = true := by decide
    refine ⟨c8r1180targets, c8r1180choice, ?_, checked⟩
    intro S h
    simp only [c8r1180targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 25 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 23 _ (by rfl)))
  have c8r1181_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)] := by
    let c8r1181targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
    let c8r1181choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1181targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)] c8r1181choice = true := by decide
    refine ⟨c8r1181targets, c8r1181choice, ?_, checked⟩
    intro S h
    simp only [c8r1181targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 26 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 26 _ (by rfl)))
  have c8r1182_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)] := by
    let c8r1182targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
    let c8r1182choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1182targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)] c8r1182choice = true := by decide
    refine ⟨c8r1182targets, c8r1182choice, ?_, checked⟩
    intro S h
    simp only [c8r1182targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 27 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 28 _ (by rfl)))
  have c8r1183_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)] := by
    let c8r1183targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
    let c8r1183choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1183targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)] c8r1183choice = true := by decide
    refine ⟨c8r1183targets, c8r1183choice, ?_, checked⟩
    intro S h
    simp only [c8r1183targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 28 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L9_lift _ (familyLookup_sound F9B003L9 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 30 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1176_closed
  · subst row; exact c8r1177_closed
  · subst row; exact c8r1178_closed
  · subst row; exact c8r1179_closed
  · subst row; exact c8r1180_closed
  · subst row; exact c8r1181_closed
  · subst row; exact c8r1182_closed
  · subst row; exact c8r1183_closed
theorem C8R01152_closed (row : List GridPoint) (h : FamilyMember row F8B000L36) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L36, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01152G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01152G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01152G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01152G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01152G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01152G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01152G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01152G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01152G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01152G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01152G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01152G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01152G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01152G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01152G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01152G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01152G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01152G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01152G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01152G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01152G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01152G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01152G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01152G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01152G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01152G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01152G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01152G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01152G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01152G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01152G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01152G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
