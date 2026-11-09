import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00320_closed (row : List GridPoint) (h : FamilyMember row F8B000L10) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r320_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,5)] := by
    let c8r320targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)]]
    let c8r320choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,6),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,6),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r320targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,5)] c8r320choice = true := by decide
    refine ⟨c8r320targets, c8r320choice, ?_, checked⟩
    intro S h
    simp only [c8r320targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 3 _ (by rfl)))
  have c8r321_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2)] := by
    let c8r321targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)]]
    let c8r321choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r321targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2)] c8r321choice = true := by decide
    refine ⟨c8r321targets, c8r321choice, ?_, checked⟩
    intro S h
    simp only [c8r321targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 8 _ (by rfl)))
  have c8r322_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3)] := by
    let c8r322targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)]]
    let c8r322choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r322targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3)] c8r322choice = true := by decide
    refine ⟨c8r322targets, c8r322choice, ?_, checked⟩
    intro S h
    simp only [c8r322targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 11 _ (by rfl)))
  have c8r323_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4)] := by
    let c8r323targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)]]
    let c8r323choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r323targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4)] c8r323choice = true := by decide
    refine ⟨c8r323targets, c8r323choice, ?_, checked⟩
    intro S h
    simp only [c8r323targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 14 _ (by rfl)))
  have c8r324_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,2)] := by
    let c8r324targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)]]
    let c8r324choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0))),((3,3),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r324targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,2)] c8r324choice = true := by decide
    refine ⟨c8r324targets, c8r324choice, ?_, checked⟩
    intro S h
    simp only [c8r324targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 17 _ (by rfl)))
  have c8r325_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4)] := by
    let c8r325targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]]
    let c8r325choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r325targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4)] c8r325choice = true := by decide
    refine ⟨c8r325targets, c8r325choice, ?_, checked⟩
    intro S h
    simp only [c8r325targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 20 _ (by rfl)))
  have c8r326_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,3)] := by
    let c8r326targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)]]
    let c8r326choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r326targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,3)] c8r326choice = true := by decide
    refine ⟨c8r326targets, c8r326choice, ?_, checked⟩
    intro S h
    simp only [c8r326targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 23 _ (by rfl)))
  have c8r327_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(2,5)] := by
    let c8r327targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)]]
    let c8r327choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,6),(11,(0,0))),((3,4),(12,(0,0))),((3,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r327targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(2,5)] c8r327choice = true := by decide
    refine ⟨c8r327targets, c8r327choice, ?_, checked⟩
    intro S h
    simp only [c8r327targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 26 _ (by rfl)))
  have c8r328_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(3,4)] := by
    let c8r328targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)]]
    let c8r328choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,3),(12,(0,0))),((3,5),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r328targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(3,4)] c8r328choice = true := by decide
    refine ⟨c8r328targets, c8r328choice, ?_, checked⟩
    intro S h
    simp only [c8r328targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 29 _ (by rfl)))
  have c8r329_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c8r329targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c8r329choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r329targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2)] c8r329choice = true := by decide
    refine ⟨c8r329targets, c8r329choice, ?_, checked⟩
    intro S h
    simp only [c8r329targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 2 _ (by rfl)))
  have c8r330_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3)] := by
    let c8r330targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c8r330choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r330targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3)] c8r330choice = true := by decide
    refine ⟨c8r330targets, c8r330choice, ?_, checked⟩
    intro S h
    simp only [c8r330targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 6 _ (by rfl)))
  have c8r331_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1)] := by
    let c8r331targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)]]
    let c8r331choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r331targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1)] c8r331choice = true := by decide
    refine ⟨c8r331targets, c8r331choice, ?_, checked⟩
    intro S h
    simp only [c8r331targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 9 _ (by rfl)))
  have c8r332_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2)] := by
    let c8r332targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)]]
    let c8r332choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r332targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2)] c8r332choice = true := by decide
    refine ⟨c8r332targets, c8r332choice, ?_, checked⟩
    intro S h
    simp only [c8r332targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 11 _ (by rfl)))
  have c8r333_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4)] := by
    let c8r333targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)]]
    let c8r333choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r333targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4)] c8r333choice = true := by decide
    refine ⟨c8r333targets, c8r333choice, ?_, checked⟩
    intro S h
    simp only [c8r333targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 15 _ (by rfl)))
  have c8r334_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2)] := by
    let c8r334targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)]]
    let c8r334choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r334targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2)] c8r334choice = true := by decide
    refine ⟨c8r334targets, c8r334choice, ?_, checked⟩
    intro S h
    simp only [c8r334targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 18 _ (by rfl)))
  have c8r335_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3)] := by
    let c8r335targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)]]
    let c8r335choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r335targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3)] c8r335choice = true := by decide
    refine ⟨c8r335targets, c8r335choice, ?_, checked⟩
    intro S h
    simp only [c8r335targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 20 _ (by rfl)))
  have c8r336_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2)] := by
    let c8r336targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)]]
    let c8r336choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r336targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2)] c8r336choice = true := by decide
    refine ⟨c8r336targets, c8r336choice, ?_, checked⟩
    intro S h
    simp only [c8r336targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 24 _ (by rfl)))
  have c8r337_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3)] := by
    let c8r337targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)]]
    let c8r337choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r337targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3)] c8r337choice = true := by decide
    refine ⟨c8r337targets, c8r337choice, ?_, checked⟩
    intro S h
    simp only [c8r337targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 27 _ (by rfl)))
  have c8r338_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2)] := by
    let c8r338targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)]]
    let c8r338choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r338targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2)] c8r338choice = true := by decide
    refine ⟨c8r338targets, c8r338choice, ?_, checked⟩
    intro S h
    simp only [c8r338targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 30 _ (by rfl)))
  have c8r339_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5)] := by
    let c8r339targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)]]
    let c8r339choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((1,5),(8,(0,0))),((2,2),(9,(0,0))),((2,6),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0))),((3,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r339targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5)] c8r339choice = true := by decide
    refine ⟨c8r339targets, c8r339choice, ?_, checked⟩
    intro S h
    simp only [c8r339targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 2 _ (by rfl)))
  have c8r340_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3)] := by
    let c8r340targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)]]
    let c8r340choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r340targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3)] c8r340choice = true := by decide
    refine ⟨c8r340targets, c8r340choice, ?_, checked⟩
    intro S h
    simp only [c8r340targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 5 _ (by rfl)))
  have c8r341_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4)] := by
    let c8r341targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)]]
    let c8r341choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,3),(10,(0,0))),((3,5),(11,(0,0))),((4,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r341targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4)] c8r341choice = true := by decide
    refine ⟨c8r341targets, c8r341choice, ?_, checked⟩
    intro S h
    simp only [c8r341targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 7 _ (by rfl)))
  have c8r342_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3)] := by
    let c8r342targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)]]
    let c8r342choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r342targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3)] c8r342choice = true := by decide
    refine ⟨c8r342targets, c8r342choice, ?_, checked⟩
    intro S h
    simp only [c8r342targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 11 _ (by rfl)))
  have c8r343_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4)] := by
    let c8r343targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)]]
    let c8r343choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,5),(11,(0,0))),((4,3),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r343targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4)] c8r343choice = true := by decide
    refine ⟨c8r343targets, c8r343choice, ?_, checked⟩
    intro S h
    simp only [c8r343targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 14 _ (by rfl)))
  have c8r344_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(4,3)] := by
    let c8r344targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)]]
    let c8r344choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r344targets [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(4,3)] c8r344choice = true := by decide
    refine ⟨c8r344targets, c8r344choice, ?_, checked⟩
    intro S h
    simp only [c8r344targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 17 _ (by rfl)))
  have c8r345_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4)] := by
    let c8r345targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)]]
    let c8r345choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((1,5),(9,(0,0))),((2,1),(10,(0,0))),((2,5),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r345targets [(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4)] c8r345choice = true := by decide
    refine ⟨c8r345targets, c8r345choice, ?_, checked⟩
    intro S h
    simp only [c8r345targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 23 _ (by rfl)))
  have c8r346_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r346targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r346choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r346targets [(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3)] c8r346choice = true := by decide
    refine ⟨c8r346targets, c8r346choice, ?_, checked⟩
    intro S h
    simp only [c8r346targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 29 _ (by rfl)))
  have c8r347_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r347targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r347choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r347targets [(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0)] c8r347choice = true := by decide
    refine ⟨c8r347targets, c8r347choice, ?_, checked⟩
    intro S h
    simp only [c8r347targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 0 _ (by rfl)))
  have c8r348_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r348targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r348choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r348targets [(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1)] c8r348choice = true := by decide
    refine ⟨c8r348targets, c8r348choice, ?_, checked⟩
    intro S h
    simp only [c8r348targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 2 _ (by rfl)))
  have c8r349_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r349targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r349choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r349targets [(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2)] c8r349choice = true := by decide
    refine ⟨c8r349targets, c8r349choice, ?_, checked⟩
    intro S h
    simp only [c8r349targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 4 _ (by rfl)))
  have c8r350_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r350targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r350choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,5),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r350targets [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4)] c8r350choice = true := by decide
    refine ⟨c8r350targets, c8r350choice, ?_, checked⟩
    intro S h
    simp only [c8r350targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 10 _ (by rfl)))
  have c8r351_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r351targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r351choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r351targets [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1)] c8r351choice = true := by decide
    refine ⟨c8r351targets, c8r351choice, ?_, checked⟩
    intro S h
    simp only [c8r351targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 14 _ (by rfl)))
  simp only [F8B000L10, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c8r320_closed
  · subst row; exact c8r321_closed
  · subst row; exact c8r322_closed
  · subst row; exact c8r323_closed
  · subst row; exact c8r324_closed
  · subst row; exact c8r325_closed
  · subst row; exact c8r326_closed
  · subst row; exact c8r327_closed
  · subst row; exact c8r328_closed
  · subst row; exact c8r329_closed
  · subst row; exact c8r330_closed
  · subst row; exact c8r331_closed
  · subst row; exact c8r332_closed
  · subst row; exact c8r333_closed
  · subst row; exact c8r334_closed
  · subst row; exact c8r335_closed
  · subst row; exact c8r336_closed
  · subst row; exact c8r337_closed
  · subst row; exact c8r338_closed
  · subst row; exact c8r339_closed
  · subst row; exact c8r340_closed
  · subst row; exact c8r341_closed
  · subst row; exact c8r342_closed
  · subst row; exact c8r343_closed
  · subst row; exact c8r344_closed
  · subst row; exact c8r345_closed
  · subst row; exact c8r346_closed
  · subst row; exact c8r347_closed
  · subst row; exact c8r348_closed
  · subst row; exact c8r349_closed
  · subst row; exact c8r350_closed
  · subst row; exact c8r351_closed
end Polyomino57
