import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01312G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1312_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)] := by
    let c8r1312targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c8r1312choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1312targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)] c8r1312choice = true := by decide
    refine ⟨c8r1312targets, c8r1312choice, ?_, checked⟩
    intro S h
    simp only [c8r1312targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 21 _ (by rfl)))
  have c8r1313_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)] := by
    let c8r1313targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c8r1313choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1313targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)] c8r1313choice = true := by decide
    refine ⟨c8r1313targets, c8r1313choice, ?_, checked⟩
    intro S h
    simp only [c8r1313targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 25 _ (by rfl)))
  have c8r1314_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)] := by
    let c8r1314targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c8r1314choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1314targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)] c8r1314choice = true := by decide
    refine ⟨c8r1314targets, c8r1314choice, ?_, checked⟩
    intro S h
    simp only [c8r1314targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 28 _ (by rfl)))
  have c8r1315_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)] := by
    let c8r1315targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c8r1315choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1315targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)] c8r1315choice = true := by decide
    refine ⟨c8r1315targets, c8r1315choice, ?_, checked⟩
    intro S h
    simp only [c8r1315targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 30 _ (by rfl)))
  have c8r1316_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)] := by
    let c8r1316targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c8r1316choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1316targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)] c8r1316choice = true := by decide
    refine ⟨c8r1316targets, c8r1316choice, ?_, checked⟩
    intro S h
    simp only [c8r1316targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 1 _ (by rfl)))
  have c8r1317_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)] := by
    let c8r1317targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c8r1317choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1317targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)] c8r1317choice = true := by decide
    refine ⟨c8r1317targets, c8r1317choice, ?_, checked⟩
    intro S h
    simp only [c8r1317targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 4 _ (by rfl)))
  have c8r1318_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)] := by
    let c8r1318targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c8r1318choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1318targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)] c8r1318choice = true := by decide
    refine ⟨c8r1318targets, c8r1318choice, ?_, checked⟩
    intro S h
    simp only [c8r1318targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 7 _ (by rfl)))
  have c8r1319_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c8r1319targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1319choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1319targets [(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] c8r1319choice = true := by decide
    refine ⟨c8r1319targets, c8r1319choice, ?_, checked⟩
    intro S h
    simp only [c8r1319targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 12 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1312_closed
  · subst row; exact c8r1313_closed
  · subst row; exact c8r1314_closed
  · subst row; exact c8r1315_closed
  · subst row; exact c8r1316_closed
  · subst row; exact c8r1317_closed
  · subst row; exact c8r1318_closed
  · subst row; exact c8r1319_closed
theorem C8R01312G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1320_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1320targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1320choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1320targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)] c8r1320choice = true := by decide
    refine ⟨c8r1320targets, c8r1320choice, ?_, checked⟩
    intro S h
    simp only [c8r1320targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 17 _ (by rfl)))
  have c8r1321_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r1321targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r1321choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1321targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)] c8r1321choice = true := by decide
    refine ⟨c8r1321targets, c8r1321choice, ?_, checked⟩
    intro S h
    simp only [c8r1321targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L18_lift _ (familyLookup_sound F9B003L18 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 20 _ (by rfl)))
  have c8r1322_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r1322targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r1322choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1322targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)] c8r1322choice = true := by decide
    refine ⟨c8r1322targets, c8r1322choice, ?_, checked⟩
    intro S h
    simp only [c8r1322targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L18_lift _ (familyLookup_sound F9B003L18 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 22 _ (by rfl)))
  have c8r1323_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r1323targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r1323choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1323targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)] c8r1323choice = true := by decide
    refine ⟨c8r1323targets, c8r1323choice, ?_, checked⟩
    intro S h
    simp only [c8r1323targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L18_lift _ (familyLookup_sound F9B003L18 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 24 _ (by rfl)))
  have c8r1324_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] := by
    let c8r1324targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
    let c8r1324choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1324targets [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] c8r1324choice = true := by decide
    refine ⟨c8r1324targets, c8r1324choice, ?_, checked⟩
    intro S h
    simp only [c8r1324targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 31 _ (by rfl)))
  have c8r1325_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c8r1325targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1325choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1325targets [(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)] c8r1325choice = true := by decide
    refine ⟨c8r1325targets, c8r1325choice, ?_, checked⟩
    intro S h
    simp only [c8r1325targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 4 _ (by rfl)))
  have c8r1326_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)] := by
    let c8r1326targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)]]
    let c8r1326choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1326targets [(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)] c8r1326choice = true := by decide
    refine ⟨c8r1326targets, c8r1326choice, ?_, checked⟩
    intro S h
    simp only [c8r1326targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 8 _ (by rfl)))
  have c8r1327_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)] := by
    let c8r1327targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)]]
    let c8r1327choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1327targets [(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)] c8r1327choice = true := by decide
    refine ⟨c8r1327targets, c8r1327choice, ?_, checked⟩
    intro S h
    simp only [c8r1327targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 10 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1320_closed
  · subst row; exact c8r1321_closed
  · subst row; exact c8r1322_closed
  · subst row; exact c8r1323_closed
  · subst row; exact c8r1324_closed
  · subst row; exact c8r1325_closed
  · subst row; exact c8r1326_closed
  · subst row; exact c8r1327_closed
theorem C8R01312G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1328_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)] := by
    let c8r1328targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)]]
    let c8r1328choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1328targets [(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)] c8r1328choice = true := by decide
    refine ⟨c8r1328targets, c8r1328choice, ?_, checked⟩
    intro S h
    simp only [c8r1328targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 12 _ (by rfl)))
  have c8r1329_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)] := by
    let c8r1329targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1329choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1329targets [(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)] c8r1329choice = true := by decide
    refine ⟨c8r1329targets, c8r1329choice, ?_, checked⟩
    intro S h
    simp only [c8r1329targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 17 _ (by rfl)))
  have c8r1330_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1330targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1330choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1330targets [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)] c8r1330choice = true := by decide
    refine ⟨c8r1330targets, c8r1330choice, ?_, checked⟩
    intro S h
    simp only [c8r1330targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 24 _ (by rfl)))
  have c8r1331_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r1331targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r1331choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1331targets [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)] c8r1331choice = true := by decide
    refine ⟨c8r1331targets, c8r1331choice, ?_, checked⟩
    intro S h
    simp only [c8r1331targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 27 _ (by rfl)))
  have c8r1332_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r1332targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r1332choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1332targets [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)] c8r1332choice = true := by decide
    refine ⟨c8r1332targets, c8r1332choice, ?_, checked⟩
    intro S h
    simp only [c8r1332targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 29 _ (by rfl)))
  have c8r1333_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r1333targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r1333choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1333targets [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)] c8r1333choice = true := by decide
    refine ⟨c8r1333targets, c8r1333choice, ?_, checked⟩
    intro S h
    simp only [c8r1333targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 31 _ (by rfl)))
  have c8r1334_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)] := by
    let c8r1334targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1334choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1334targets [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)] c8r1334choice = true := by decide
    refine ⟨c8r1334targets, c8r1334choice, ?_, checked⟩
    intro S h
    simp only [c8r1334targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 2 _ (by rfl)))
  have c8r1335_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)] := by
    let c8r1335targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c8r1335choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1335targets [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)] c8r1335choice = true := by decide
    refine ⟨c8r1335targets, c8r1335choice, ?_, checked⟩
    intro S h
    simp only [c8r1335targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 4 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1328_closed
  · subst row; exact c8r1329_closed
  · subst row; exact c8r1330_closed
  · subst row; exact c8r1331_closed
  · subst row; exact c8r1332_closed
  · subst row; exact c8r1333_closed
  · subst row; exact c8r1334_closed
  · subst row; exact c8r1335_closed
theorem C8R01312G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1336_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)] := by
    let c8r1336targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c8r1336choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1336targets [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)] c8r1336choice = true := by decide
    refine ⟨c8r1336targets, c8r1336choice, ?_, checked⟩
    intro S h
    simp only [c8r1336targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 7 _ (by rfl)))
  have c8r1337_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)] := by
    let c8r1337targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c8r1337choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1337targets [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)] c8r1337choice = true := by decide
    refine ⟨c8r1337targets, c8r1337choice, ?_, checked⟩
    intro S h
    simp only [c8r1337targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 10 _ (by rfl)))
  have c8r1338_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r1338targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r1338choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1338targets [(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)] c8r1338choice = true := by decide
    refine ⟨c8r1338targets, c8r1338choice, ?_, checked⟩
    intro S h
    simp only [c8r1338targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 15 _ (by rfl)))
  have c8r1339_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)] := by
    let c8r1339targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1339choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1339targets [(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)] c8r1339choice = true := by decide
    refine ⟨c8r1339targets, c8r1339choice, ?_, checked⟩
    intro S h
    simp only [c8r1339targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 20 _ (by rfl)))
  have c8r1340_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)] := by
    let c8r1340targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c8r1340choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1340targets [(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)] c8r1340choice = true := by decide
    refine ⟨c8r1340targets, c8r1340choice, ?_, checked⟩
    intro S h
    simp only [c8r1340targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 22 _ (by rfl)))
  have c8r1341_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)] := by
    let c8r1341targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c8r1341choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1341targets [(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)] c8r1341choice = true := by decide
    refine ⟨c8r1341targets, c8r1341choice, ?_, checked⟩
    intro S h
    simp only [c8r1341targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 24 _ (by rfl)))
  have c8r1342_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)] := by
    let c8r1342targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c8r1342choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1342targets [(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)] c8r1342choice = true := by decide
    refine ⟨c8r1342targets, c8r1342choice, ?_, checked⟩
    intro S h
    simp only [c8r1342targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 28 _ (by rfl)))
  have c8r1343_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r1343targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1343choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1343targets [(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)] c8r1343choice = true := by decide
    refine ⟨c8r1343targets, c8r1343choice, ?_, checked⟩
    intro S h
    simp only [c8r1343targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 2 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1336_closed
  · subst row; exact c8r1337_closed
  · subst row; exact c8r1338_closed
  · subst row; exact c8r1339_closed
  · subst row; exact c8r1340_closed
  · subst row; exact c8r1341_closed
  · subst row; exact c8r1342_closed
  · subst row; exact c8r1343_closed
theorem C8R01312_closed (row : List GridPoint) (h : FamilyMember row F8B000L41) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L41, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01312G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01312G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01312G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01312G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01312G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01312G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01312G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01312G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01312G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01312G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01312G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01312G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01312G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01312G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01312G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01312G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01312G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01312G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01312G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01312G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01312G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01312G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01312G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01312G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01312G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01312G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01312G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01312G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01312G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01312G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01312G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01312G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
