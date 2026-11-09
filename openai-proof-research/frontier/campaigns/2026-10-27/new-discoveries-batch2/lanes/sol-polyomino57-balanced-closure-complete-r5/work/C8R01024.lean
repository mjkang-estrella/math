import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01024G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1024_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c8r1024targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c8r1024choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1024targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)] c8r1024choice = true := by decide
    refine ⟨c8r1024targets, c8r1024choice, ?_, checked⟩
    intro S h
    simp only [c8r1024targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 23 _ (by rfl)))
  have c8r1025_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)] := by
    let c8r1025targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c8r1025choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1025targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)] c8r1025choice = true := by decide
    refine ⟨c8r1025targets, c8r1025choice, ?_, checked⟩
    intro S h
    simp only [c8r1025targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 26 _ (by rfl)))
  have c8r1026_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r1026targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1026choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1026targets [(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)] c8r1026choice = true := by decide
    refine ⟨c8r1026targets, c8r1026choice, ?_, checked⟩
    intro S h
    simp only [c8r1026targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 31 _ (by rfl)))
  have c8r1027_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1027targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1027choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((1,5),(8,(0,0))),((2,-1),(9,(0,1))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1027targets [(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)] c8r1027choice = true := by decide
    refine ⟨c8r1027targets, c8r1027choice, ?_, checked⟩
    intro S h
    simp only [c8r1027targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 5 _ (by rfl)))
  have c8r1028_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r1028targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r1028choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1028targets [(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)] c8r1028choice = true := by decide
    refine ⟨c8r1028targets, c8r1028choice, ?_, checked⟩
    intro S h
    simp only [c8r1028targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 11 _ (by rfl)))
  have c8r1029_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c8r1029targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c8r1029choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1029targets [(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)] c8r1029choice = true := by decide
    refine ⟨c8r1029targets, c8r1029choice, ?_, checked⟩
    intro S h
    simp only [c8r1029targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 15 _ (by rfl)))
  have c8r1030_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r1030targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r1030choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1030targets [(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] c8r1030choice = true := by decide
    refine ⟨c8r1030targets, c8r1030choice, ?_, checked⟩
    intro S h
    simp only [c8r1030targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 18 _ (by rfl)))
  have c8r1031_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r1031targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r1031choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1031targets [(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] c8r1031choice = true := by decide
    refine ⟨c8r1031targets, c8r1031choice, ?_, checked⟩
    intro S h
    simp only [c8r1031targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 20 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1024_closed
  · subst row; exact c8r1025_closed
  · subst row; exact c8r1026_closed
  · subst row; exact c8r1027_closed
  · subst row; exact c8r1028_closed
  · subst row; exact c8r1029_closed
  · subst row; exact c8r1030_closed
  · subst row; exact c8r1031_closed
theorem C8R01024G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1032_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r1032targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r1032choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1032targets [(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] c8r1032choice = true := by decide
    refine ⟨c8r1032targets, c8r1032choice, ?_, checked⟩
    intro S h
    simp only [c8r1032targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 22 _ (by rfl)))
  have c8r1033_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r1033targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r1033choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((1,5),(8,(0,0))),((2,-1),(9,(0,1))),((2,5),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1033targets [(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] c8r1033choice = true := by decide
    refine ⟨c8r1033targets, c8r1033choice, ?_, checked⟩
    intro S h
    simp only [c8r1033targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 0 _ (by rfl)))
  have c8r1034_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c8r1034targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c8r1034choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((1,5),(8,(0,0))),((2,-1),(9,(0,1))),((2,6),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0))),((3,5),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1034targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] c8r1034choice = true := by decide
    refine ⟨c8r1034targets, c8r1034choice, ?_, checked⟩
    intro S h
    simp only [c8r1034targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 8 _ (by rfl)))
  have c8r1035_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] := by
    let c8r1035targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)]]
    let c8r1035choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0))),((4,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1035targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] c8r1035choice = true := by decide
    refine ⟨c8r1035targets, c8r1035choice, ?_, checked⟩
    intro S h
    simp only [c8r1035targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 13 _ (by rfl)))
  have c8r1036_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] := by
    let c8r1036targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]
    let c8r1036choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1036targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] c8r1036choice = true := by decide
    refine ⟨c8r1036targets, c8r1036choice, ?_, checked⟩
    intro S h
    simp only [c8r1036targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 17 _ (by rfl)))
  have c8r1037_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] := by
    let c8r1037targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c8r1037choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1037targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] c8r1037choice = true := by decide
    refine ⟨c8r1037targets, c8r1037choice, ?_, checked⟩
    intro S h
    simp only [c8r1037targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 20 _ (by rfl)))
  have c8r1038_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] := by
    let c8r1038targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c8r1038choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1038targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] c8r1038choice = true := by decide
    refine ⟨c8r1038targets, c8r1038choice, ?_, checked⟩
    intro S h
    simp only [c8r1038targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 22 _ (by rfl)))
  have c8r1039_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c8r1039targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c8r1039choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,5),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1039targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] c8r1039choice = true := by decide
    refine ⟨c8r1039targets, c8r1039choice, ?_, checked⟩
    intro S h
    simp only [c8r1039targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 24 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1032_closed
  · subst row; exact c8r1033_closed
  · subst row; exact c8r1034_closed
  · subst row; exact c8r1035_closed
  · subst row; exact c8r1036_closed
  · subst row; exact c8r1037_closed
  · subst row; exact c8r1038_closed
  · subst row; exact c8r1039_closed
theorem C8R01024G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1040_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c8r1040targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c8r1040choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1040targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)] c8r1040choice = true := by decide
    refine ⟨c8r1040targets, c8r1040choice, ?_, checked⟩
    intro S h
    simp only [c8r1040targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 28 _ (by rfl)))
  have c8r1041_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)] := by
    let c8r1041targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)]]
    let c8r1041choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1041targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)] c8r1041choice = true := by decide
    refine ⟨c8r1041targets, c8r1041choice, ?_, checked⟩
    intro S h
    simp only [c8r1041targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 31 _ (by rfl)))
  have c8r1042_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)] := by
    let c8r1042targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3)]]
    let c8r1042choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,0),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1042targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)] c8r1042choice = true := by decide
    refine ⟨c8r1042targets, c8r1042choice, ?_, checked⟩
    intro S h
    simp only [c8r1042targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 2 _ (by rfl)))
  have c8r1043_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)] := by
    let c8r1043targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(5,0)]]
    let c8r1043choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,-1),(13,(0,1))),((4,1),(14,(0,0))),((5,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1043targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)] c8r1043choice = true := by decide
    refine ⟨c8r1043targets, c8r1043choice, ?_, checked⟩
    intro S h
    simp only [c8r1043targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 4 _ (by rfl)))
  have c8r1044_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)] := by
    let c8r1044targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c8r1044choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1044targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)] c8r1044choice = true := by decide
    refine ⟨c8r1044targets, c8r1044choice, ?_, checked⟩
    intro S h
    simp only [c8r1044targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 7 _ (by rfl)))
  have c8r1045_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)] := by
    let c8r1045targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)]]
    let c8r1045choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1045targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)] c8r1045choice = true := by decide
    refine ⟨c8r1045targets, c8r1045choice, ?_, checked⟩
    intro S h
    simp only [c8r1045targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 10 _ (by rfl)))
  have c8r1046_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)] := by
    let c8r1046targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)]]
    let c8r1046choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1046targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)] c8r1046choice = true := by decide
    refine ⟨c8r1046targets, c8r1046choice, ?_, checked⟩
    intro S h
    simp only [c8r1046targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 13 _ (by rfl)))
  have c8r1047_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)] := by
    let c8r1047targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c8r1047choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1047targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)] c8r1047choice = true := by decide
    refine ⟨c8r1047targets, c8r1047choice, ?_, checked⟩
    intro S h
    simp only [c8r1047targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 16 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1040_closed
  · subst row; exact c8r1041_closed
  · subst row; exact c8r1042_closed
  · subst row; exact c8r1043_closed
  · subst row; exact c8r1044_closed
  · subst row; exact c8r1045_closed
  · subst row; exact c8r1046_closed
  · subst row; exact c8r1047_closed
theorem C8R01024G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1048_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)] := by
    let c8r1048targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c8r1048choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1048targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)] c8r1048choice = true := by decide
    refine ⟨c8r1048targets, c8r1048choice, ?_, checked⟩
    intro S h
    simp only [c8r1048targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 19 _ (by rfl)))
  have c8r1049_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)] := by
    let c8r1049targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c8r1049choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,5),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1049targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)] c8r1049choice = true := by decide
    refine ⟨c8r1049targets, c8r1049choice, ?_, checked⟩
    intro S h
    simp only [c8r1049targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 22 _ (by rfl)))
  have c8r1050_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)] := by
    let c8r1050targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c8r1050choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0))),((4,4),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1050targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)] c8r1050choice = true := by decide
    refine ⟨c8r1050targets, c8r1050choice, ?_, checked⟩
    intro S h
    simp only [c8r1050targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 25 _ (by rfl)))
  have c8r1051_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r1051targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1051choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1051targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)] c8r1051choice = true := by decide
    refine ⟨c8r1051targets, c8r1051choice, ?_, checked⟩
    intro S h
    simp only [c8r1051targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 30 _ (by rfl)))
  have c8r1052_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)] := by
    let c8r1052targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
    let c8r1052choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1052targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)] c8r1052choice = true := by decide
    refine ⟨c8r1052targets, c8r1052choice, ?_, checked⟩
    intro S h
    simp only [c8r1052targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 0 _ (by rfl)))
  have c8r1053_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c8r1053targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c8r1053choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1053targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)] c8r1053choice = true := by decide
    refine ⟨c8r1053targets, c8r1053choice, ?_, checked⟩
    intro S h
    simp only [c8r1053targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 2 _ (by rfl)))
  have c8r1054_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)] := by
    let c8r1054targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)]]
    let c8r1054choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1054targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)] c8r1054choice = true := by decide
    refine ⟨c8r1054targets, c8r1054choice, ?_, checked⟩
    intro S h
    simp only [c8r1054targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L59_lift _ (familyLookup_sound F9B002L59 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 6 _ (by rfl)))
  have c8r1055_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)] := by
    let c8r1055targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)]]
    let c8r1055choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1055targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)] c8r1055choice = true := by decide
    refine ⟨c8r1055targets, c8r1055choice, ?_, checked⟩
    intro S h
    simp only [c8r1055targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 9 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1048_closed
  · subst row; exact c8r1049_closed
  · subst row; exact c8r1050_closed
  · subst row; exact c8r1051_closed
  · subst row; exact c8r1052_closed
  · subst row; exact c8r1053_closed
  · subst row; exact c8r1054_closed
  · subst row; exact c8r1055_closed
theorem C8R01024_closed (row : List GridPoint) (h : FamilyMember row F8B000L32) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L32, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01024G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01024G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01024G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01024G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01024G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01024G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01024G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01024G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01024G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01024G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01024G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01024G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01024G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01024G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01024G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01024G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01024G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01024G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01024G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01024G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01024G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01024G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01024G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01024G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01024G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01024G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01024G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01024G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01024G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01024G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01024G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01024G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
