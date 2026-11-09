import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01344G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1344_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1344targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1344choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1344targets [(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)] c8r1344choice = true := by decide
    refine ⟨c8r1344targets, c8r1344choice, ?_, checked⟩
    intro S h
    simp only [c8r1344targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 10 _ (by rfl)))
  have c8r1345_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r1345targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r1345choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1345targets [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)] c8r1345choice = true := by decide
    refine ⟨c8r1345targets, c8r1345choice, ?_, checked⟩
    intro S h
    simp only [c8r1345targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 18 _ (by rfl)))
  have c8r1346_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c8r1346targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c8r1346choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1346targets [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)] c8r1346choice = true := by decide
    refine ⟨c8r1346targets, c8r1346choice, ?_, checked⟩
    intro S h
    simp only [c8r1346targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L48_lift _ (familyLookup_sound F9B003L48 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 22 _ (by rfl)))
  have c8r1347_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r1347targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r1347choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1347targets [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)] c8r1347choice = true := by decide
    refine ⟨c8r1347targets, c8r1347choice, ?_, checked⟩
    intro S h
    simp only [c8r1347targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 25 _ (by rfl)))
  have c8r1348_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r1348targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r1348choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1348targets [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)] c8r1348choice = true := by decide
    refine ⟨c8r1348targets, c8r1348choice, ?_, checked⟩
    intro S h
    simp only [c8r1348targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 27 _ (by rfl)))
  have c8r1349_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r1349targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r1349choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1349targets [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)] c8r1349choice = true := by decide
    refine ⟨c8r1349targets, c8r1349choice, ?_, checked⟩
    intro S h
    simp only [c8r1349targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 29 _ (by rfl)))
  have c8r1350_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r1350targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r1350choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1350targets [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)] c8r1350choice = true := by decide
    refine ⟨c8r1350targets, c8r1350choice, ?_, checked⟩
    intro S h
    simp only [c8r1350targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 0 _ (by rfl)))
  have c8r1351_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c8r1351targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c8r1351choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1351targets [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)] c8r1351choice = true := by decide
    refine ⟨c8r1351targets, c8r1351choice, ?_, checked⟩
    intro S h
    simp only [c8r1351targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 3 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1344_closed
  · subst row; exact c8r1345_closed
  · subst row; exact c8r1346_closed
  · subst row; exact c8r1347_closed
  · subst row; exact c8r1348_closed
  · subst row; exact c8r1349_closed
  · subst row; exact c8r1350_closed
  · subst row; exact c8r1351_closed
theorem C8R01344G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1352_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c8r1352targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c8r1352choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1352targets [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)] c8r1352choice = true := by decide
    refine ⟨c8r1352targets, c8r1352choice, ?_, checked⟩
    intro S h
    simp only [c8r1352targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 5 _ (by rfl)))
  have c8r1353_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c8r1353targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c8r1353choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1353targets [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)] c8r1353choice = true := by decide
    refine ⟨c8r1353targets, c8r1353choice, ?_, checked⟩
    intro S h
    simp only [c8r1353targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 8 _ (by rfl)))
  have c8r1354_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c8r1354targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c8r1354choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1354targets [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)] c8r1354choice = true := by decide
    refine ⟨c8r1354targets, c8r1354choice, ?_, checked⟩
    intro S h
    simp only [c8r1354targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 11 _ (by rfl)))
  have c8r1355_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c8r1355targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c8r1355choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1355targets [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)] c8r1355choice = true := by decide
    refine ⟨c8r1355targets, c8r1355choice, ?_, checked⟩
    intro S h
    simp only [c8r1355targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L22_lift _ (familyLookup_sound F9B003L22 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 14 _ (by rfl)))
  have c8r1356_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)] := by
    let c8r1356targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c8r1356choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1356targets [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)] c8r1356choice = true := by decide
    refine ⟨c8r1356targets, c8r1356choice, ?_, checked⟩
    intro S h
    simp only [c8r1356targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 17 _ (by rfl)))
  have c8r1357_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)] := by
    let c8r1357targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1357choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1357targets [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)] c8r1357choice = true := by decide
    refine ⟨c8r1357targets, c8r1357choice, ?_, checked⟩
    intro S h
    simp only [c8r1357targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 22 _ (by rfl)))
  have c8r1358_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)] := by
    let c8r1358targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c8r1358choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1358targets [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)] c8r1358choice = true := by decide
    refine ⟨c8r1358targets, c8r1358choice, ?_, checked⟩
    intro S h
    simp only [c8r1358targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 24 _ (by rfl)))
  have c8r1359_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)] := by
    let c8r1359targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c8r1359choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1359targets [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)] c8r1359choice = true := by decide
    refine ⟨c8r1359targets, c8r1359choice, ?_, checked⟩
    intro S h
    simp only [c8r1359targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 26 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1352_closed
  · subst row; exact c8r1353_closed
  · subst row; exact c8r1354_closed
  · subst row; exact c8r1355_closed
  · subst row; exact c8r1356_closed
  · subst row; exact c8r1357_closed
  · subst row; exact c8r1358_closed
  · subst row; exact c8r1359_closed
theorem C8R01344G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1360_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)] := by
    let c8r1360targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)]]
    let c8r1360choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1360targets [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)] c8r1360choice = true := by decide
    refine ⟨c8r1360targets, c8r1360choice, ?_, checked⟩
    intro S h
    simp only [c8r1360targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 29 _ (by rfl)))
  have c8r1361_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)] := by
    let c8r1361targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)]]
    let c8r1361choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1361targets [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)] c8r1361choice = true := by decide
    refine ⟨c8r1361targets, c8r1361choice, ?_, checked⟩
    intro S h
    simp only [c8r1361targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 31 _ (by rfl)))
  have c8r1362_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)] := by
    let c8r1362targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c8r1362choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1362targets [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)] c8r1362choice = true := by decide
    refine ⟨c8r1362targets, c8r1362choice, ?_, checked⟩
    intro S h
    simp only [c8r1362targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 3 _ (by rfl)))
  have c8r1363_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)] := by
    let c8r1363targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c8r1363choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1363targets [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)] c8r1363choice = true := by decide
    refine ⟨c8r1363targets, c8r1363choice, ?_, checked⟩
    intro S h
    simp only [c8r1363targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 6 _ (by rfl)))
  have c8r1364_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)] := by
    let c8r1364targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c8r1364choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1364targets [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)] c8r1364choice = true := by decide
    refine ⟨c8r1364targets, c8r1364choice, ?_, checked⟩
    intro S h
    simp only [c8r1364targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 8 _ (by rfl)))
  have c8r1365_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)] := by
    let c8r1365targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c8r1365choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1365targets [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)] c8r1365choice = true := by decide
    refine ⟨c8r1365targets, c8r1365choice, ?_, checked⟩
    intro S h
    simp only [c8r1365targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 11 _ (by rfl)))
  have c8r1366_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)] := by
    let c8r1366targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c8r1366choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1366targets [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)] c8r1366choice = true := by decide
    refine ⟨c8r1366targets, c8r1366choice, ?_, checked⟩
    intro S h
    simp only [c8r1366targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 14 _ (by rfl)))
  have c8r1367_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)] := by
    let c8r1367targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c8r1367choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1367targets [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)] c8r1367choice = true := by decide
    refine ⟨c8r1367targets, c8r1367choice, ?_, checked⟩
    intro S h
    simp only [c8r1367targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L23_lift _ (familyLookup_sound F9B003L23 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 17 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1360_closed
  · subst row; exact c8r1361_closed
  · subst row; exact c8r1362_closed
  · subst row; exact c8r1363_closed
  · subst row; exact c8r1364_closed
  · subst row; exact c8r1365_closed
  · subst row; exact c8r1366_closed
  · subst row; exact c8r1367_closed
theorem C8R01344G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1368_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c8r1368targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c8r1368choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1368targets [(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)] c8r1368choice = true := by decide
    refine ⟨c8r1368targets, c8r1368choice, ?_, checked⟩
    intro S h
    simp only [c8r1368targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 22 _ (by rfl)))
  have c8r1369_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r1369targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1369choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1369targets [(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)] c8r1369choice = true := by decide
    refine ⟨c8r1369targets, c8r1369choice, ?_, checked⟩
    intro S h
    simp only [c8r1369targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 27 _ (by rfl)))
  have c8r1370_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)] := by
    let c8r1370targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
    let c8r1370choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1370targets [(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)] c8r1370choice = true := by decide
    refine ⟨c8r1370targets, c8r1370choice, ?_, checked⟩
    intro S h
    simp only [c8r1370targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 29 _ (by rfl)))
  have c8r1371_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c8r1371targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c8r1371choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1371targets [(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)] c8r1371choice = true := by decide
    refine ⟨c8r1371targets, c8r1371choice, ?_, checked⟩
    intro S h
    simp only [c8r1371targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 31 _ (by rfl)))
  have c8r1372_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c8r1372targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c8r1372choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1372targets [(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)] c8r1372choice = true := by decide
    refine ⟨c8r1372targets, c8r1372choice, ?_, checked⟩
    intro S h
    simp only [c8r1372targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 3 _ (by rfl)))
  have c8r1373_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r1373targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r1373choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1373targets [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] c8r1373choice = true := by decide
    refine ⟨c8r1373targets, c8r1373choice, ?_, checked⟩
    intro S h
    simp only [c8r1373targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 11 _ (by rfl)))
  have c8r1374_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r1374targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r1374choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1374targets [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] c8r1374choice = true := by decide
    refine ⟨c8r1374targets, c8r1374choice, ?_, checked⟩
    intro S h
    simp only [c8r1374targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L25_lift _ (familyLookup_sound F9B003L25 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 14 _ (by rfl)))
  have c8r1375_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r1375targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r1375choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1375targets [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] c8r1375choice = true := by decide
    refine ⟨c8r1375targets, c8r1375choice, ?_, checked⟩
    intro S h
    simp only [c8r1375targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L49_lift _ (familyLookup_sound F9B003L49 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L24_lift _ (familyLookup_sound F9B003L24 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 16 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1368_closed
  · subst row; exact c8r1369_closed
  · subst row; exact c8r1370_closed
  · subst row; exact c8r1371_closed
  · subst row; exact c8r1372_closed
  · subst row; exact c8r1373_closed
  · subst row; exact c8r1374_closed
  · subst row; exact c8r1375_closed
theorem C8R01344_closed (row : List GridPoint) (h : FamilyMember row F8B000L42) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L42, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01344G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01344G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01344G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01344G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01344G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01344G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01344G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01344G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01344G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01344G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01344G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01344G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01344G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01344G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01344G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01344G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01344G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01344G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01344G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01344G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01344G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01344G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01344G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01344G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01344G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01344G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01344G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01344G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01344G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01344G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01344G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01344G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
