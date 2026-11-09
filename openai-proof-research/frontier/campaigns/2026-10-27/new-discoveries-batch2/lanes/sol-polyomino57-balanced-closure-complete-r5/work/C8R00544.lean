import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00544G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r544_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)] := by
    let c8r544targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)]]
    let c8r544choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r544targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)] c8r544choice = true := by decide
    refine ⟨c8r544targets, c8r544choice, ?_, checked⟩
    intro S h
    simp only [c8r544targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 23 _ (by rfl)))
  have c8r545_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)] := by
    let c8r545targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c8r545choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r545targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)] c8r545choice = true := by decide
    refine ⟨c8r545targets, c8r545choice, ?_, checked⟩
    intro S h
    simp only [c8r545targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 27 _ (by rfl)))
  have c8r546_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)] := by
    let c8r546targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)]]
    let c8r546choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r546targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)] c8r546choice = true := by decide
    refine ⟨c8r546targets, c8r546choice, ?_, checked⟩
    intro S h
    simp only [c8r546targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 30 _ (by rfl)))
  have c8r547_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)] := by
    let c8r547targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)]]
    let c8r547choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r547targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)] c8r547choice = true := by decide
    refine ⟨c8r547targets, c8r547choice, ?_, checked⟩
    intro S h
    simp only [c8r547targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 0 _ (by rfl)))
  have c8r548_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)] := by
    let c8r548targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)]]
    let c8r548choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r548targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)] c8r548choice = true := by decide
    refine ⟨c8r548targets, c8r548choice, ?_, checked⟩
    intro S h
    simp only [c8r548targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 4 _ (by rfl)))
  have c8r549_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)] := by
    let c8r549targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)]]
    let c8r549choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r549targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)] c8r549choice = true := by decide
    refine ⟨c8r549targets, c8r549choice, ?_, checked⟩
    intro S h
    simp only [c8r549targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 8 _ (by rfl)))
  have c8r550_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)] := by
    let c8r550targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)]]
    let c8r550choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r550targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)] c8r550choice = true := by decide
    refine ⟨c8r550targets, c8r550choice, ?_, checked⟩
    intro S h
    simp only [c8r550targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 11 _ (by rfl)))
  have c8r551_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)] := by
    let c8r551targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)]]
    let c8r551choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r551targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)] c8r551choice = true := by decide
    refine ⟨c8r551targets, c8r551choice, ?_, checked⟩
    intro S h
    simp only [c8r551targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 14 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r544_closed
  · subst row; exact c8r545_closed
  · subst row; exact c8r546_closed
  · subst row; exact c8r547_closed
  · subst row; exact c8r548_closed
  · subst row; exact c8r549_closed
  · subst row; exact c8r550_closed
  · subst row; exact c8r551_closed
theorem C8R00544G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r552_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)] := by
    let c8r552targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)]]
    let c8r552choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r552targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)] c8r552choice = true := by decide
    refine ⟨c8r552targets, c8r552choice, ?_, checked⟩
    intro S h
    simp only [c8r552targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 17 _ (by rfl)))
  have c8r553_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)] := by
    let c8r553targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)]]
    let c8r553choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r553targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)] c8r553choice = true := by decide
    refine ⟨c8r553targets, c8r553choice, ?_, checked⟩
    intro S h
    simp only [c8r553targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 20 _ (by rfl)))
  have c8r554_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)] := by
    let c8r554targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)]]
    let c8r554choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r554targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)] c8r554choice = true := by decide
    refine ⟨c8r554targets, c8r554choice, ?_, checked⟩
    intro S h
    simp only [c8r554targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 24 _ (by rfl)))
  have c8r555_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)] := by
    let c8r555targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)]]
    let c8r555choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r555targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)] c8r555choice = true := by decide
    refine ⟨c8r555targets, c8r555choice, ?_, checked⟩
    intro S h
    simp only [c8r555targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 27 _ (by rfl)))
  have c8r556_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)] := by
    let c8r556targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)]]
    let c8r556choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r556targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)] c8r556choice = true := by decide
    refine ⟨c8r556targets, c8r556choice, ?_, checked⟩
    intro S h
    simp only [c8r556targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 29 _ (by rfl)))
  have c8r557_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)] := by
    let c8r557targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)]]
    let c8r557choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r557targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)] c8r557choice = true := by decide
    refine ⟨c8r557targets, c8r557choice, ?_, checked⟩
    intro S h
    simp only [c8r557targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 1 _ (by rfl)))
  have c8r558_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)] := by
    let c8r558targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)]]
    let c8r558choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r558targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)] c8r558choice = true := by decide
    refine ⟨c8r558targets, c8r558choice, ?_, checked⟩
    intro S h
    simp only [c8r558targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 4 _ (by rfl)))
  have c8r559_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)] := by
    let c8r559targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)]]
    let c8r559choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r559targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)] c8r559choice = true := by decide
    refine ⟨c8r559targets, c8r559choice, ?_, checked⟩
    intro S h
    simp only [c8r559targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 7 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r552_closed
  · subst row; exact c8r553_closed
  · subst row; exact c8r554_closed
  · subst row; exact c8r555_closed
  · subst row; exact c8r556_closed
  · subst row; exact c8r557_closed
  · subst row; exact c8r558_closed
  · subst row; exact c8r559_closed
theorem C8R00544G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r560_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)] := by
    let c8r560targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)]]
    let c8r560choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,6),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0))),((3,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r560targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)] c8r560choice = true := by decide
    refine ⟨c8r560targets, c8r560choice, ?_, checked⟩
    intro S h
    simp only [c8r560targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 11 _ (by rfl)))
  have c8r561_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)] := by
    let c8r561targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)]]
    let c8r561choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r561targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)] c8r561choice = true := by decide
    refine ⟨c8r561targets, c8r561choice, ?_, checked⟩
    intro S h
    simp only [c8r561targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 14 _ (by rfl)))
  have c8r562_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)] := by
    let c8r562targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)]]
    let c8r562choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,3),(10,(0,0))),((3,5),(11,(0,0))),((4,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r562targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)] c8r562choice = true := by decide
    refine ⟨c8r562targets, c8r562choice, ?_, checked⟩
    intro S h
    simp only [c8r562targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 16 _ (by rfl)))
  have c8r563_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)] := by
    let c8r563targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)]]
    let c8r563choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r563targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)] c8r563choice = true := by decide
    refine ⟨c8r563targets, c8r563choice, ?_, checked⟩
    intro S h
    simp only [c8r563targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 20 _ (by rfl)))
  have c8r564_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)] := by
    let c8r564targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)]]
    let c8r564choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,5),(11,(0,0))),((4,3),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r564targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)] c8r564choice = true := by decide
    refine ⟨c8r564targets, c8r564choice, ?_, checked⟩
    intro S h
    simp only [c8r564targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 23 _ (by rfl)))
  have c8r565_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)] := by
    let c8r565targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)]]
    let c8r565choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r565targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)] c8r565choice = true := by decide
    refine ⟨c8r565targets, c8r565choice, ?_, checked⟩
    intro S h
    simp only [c8r565targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 26 _ (by rfl)))
  have c8r566_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)] := by
    let c8r566targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)]]
    let c8r566choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r566targets [(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)] c8r566choice = true := by decide
    refine ⟨c8r566targets, c8r566choice, ?_, checked⟩
    intro S h
    simp only [c8r566targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 0 _ (by rfl)))
  have c8r567_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r567targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r567choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r567targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)] c8r567choice = true := by decide
    refine ⟨c8r567targets, c8r567choice, ?_, checked⟩
    intro S h
    simp only [c8r567targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 6 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r560_closed
  · subst row; exact c8r561_closed
  · subst row; exact c8r562_closed
  · subst row; exact c8r563_closed
  · subst row; exact c8r564_closed
  · subst row; exact c8r565_closed
  · subst row; exact c8r566_closed
  · subst row; exact c8r567_closed
theorem C8R00544G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r568_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r568targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r568choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r568targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)] c8r568choice = true := by decide
    refine ⟨c8r568targets, c8r568choice, ?_, checked⟩
    intro S h
    simp only [c8r568targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 9 _ (by rfl)))
  have c8r569_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r569targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r569choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r569targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)] c8r569choice = true := by decide
    refine ⟨c8r569targets, c8r569choice, ?_, checked⟩
    intro S h
    simp only [c8r569targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 11 _ (by rfl)))
  have c8r570_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r570targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r570choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r570targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)] c8r570choice = true := by decide
    refine ⟨c8r570targets, c8r570choice, ?_, checked⟩
    intro S h
    simp only [c8r570targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 13 _ (by rfl)))
  have c8r571_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)] := by
    let c8r571targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c8r571choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r571targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)] c8r571choice = true := by decide
    refine ⟨c8r571targets, c8r571choice, ?_, checked⟩
    intro S h
    simp only [c8r571targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 16 _ (by rfl)))
  have c8r572_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)] := by
    let c8r572targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c8r572choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r572targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)] c8r572choice = true := by decide
    refine ⟨c8r572targets, c8r572choice, ?_, checked⟩
    intro S h
    simp only [c8r572targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 18 _ (by rfl)))
  have c8r573_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)] := by
    let c8r573targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c8r573choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r573targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)] c8r573choice = true := by decide
    refine ⟨c8r573targets, c8r573choice, ?_, checked⟩
    intro S h
    simp only [c8r573targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 21 _ (by rfl)))
  have c8r574_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)] := by
    let c8r574targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c8r574choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r574targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)] c8r574choice = true := by decide
    refine ⟨c8r574targets, c8r574choice, ?_, checked⟩
    intro S h
    simp only [c8r574targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 24 _ (by rfl)))
  have c8r575_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r575targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r575choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r575targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)] c8r575choice = true := by decide
    refine ⟨c8r575targets, c8r575choice, ?_, checked⟩
    intro S h
    simp only [c8r575targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 30 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r568_closed
  · subst row; exact c8r569_closed
  · subst row; exact c8r570_closed
  · subst row; exact c8r571_closed
  · subst row; exact c8r572_closed
  · subst row; exact c8r573_closed
  · subst row; exact c8r574_closed
  · subst row; exact c8r575_closed
theorem C8R00544_closed (row : List GridPoint) (h : FamilyMember row F8B000L17) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L17, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00544G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00544G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00544G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00544G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00544G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00544G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00544G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00544G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00544G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00544G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00544G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00544G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00544G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00544G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00544G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00544G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00544G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00544G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00544G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00544G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00544G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00544G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00544G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00544G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00544G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00544G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00544G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00544G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00544G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00544G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00544G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00544G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
