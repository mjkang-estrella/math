import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00736G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r736_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)] := by
    let c8r736targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
    let c8r736choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r736targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)] c8r736choice = true := by decide
    refine ⟨c8r736targets, c8r736choice, ?_, checked⟩
    intro S h
    simp only [c8r736targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 16 _ (by rfl)))
  have c8r737_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)] := by
    let c8r737targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)]]
    let c8r737choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r737targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)] c8r737choice = true := by decide
    refine ⟨c8r737targets, c8r737choice, ?_, checked⟩
    intro S h
    simp only [c8r737targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 20 _ (by rfl)))
  have c8r738_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)] := by
    let c8r738targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)]]
    let c8r738choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r738targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)] c8r738choice = true := by decide
    refine ⟨c8r738targets, c8r738choice, ?_, checked⟩
    intro S h
    simp only [c8r738targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 23 _ (by rfl)))
  have c8r739_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)] := by
    let c8r739targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)]]
    let c8r739choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r739targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)] c8r739choice = true := by decide
    refine ⟨c8r739targets, c8r739choice, ?_, checked⟩
    intro S h
    simp only [c8r739targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 26 _ (by rfl)))
  have c8r740_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)] := by
    let c8r740targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)]]
    let c8r740choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r740targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)] c8r740choice = true := by decide
    refine ⟨c8r740targets, c8r740choice, ?_, checked⟩
    intro S h
    simp only [c8r740targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 29 _ (by rfl)))
  have c8r741_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)] := by
    let c8r741targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)]]
    let c8r741choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r741targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)] c8r741choice = true := by decide
    refine ⟨c8r741targets, c8r741choice, ?_, checked⟩
    intro S h
    simp only [c8r741targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 31 _ (by rfl)))
  have c8r742_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)] := by
    let c8r742targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)]]
    let c8r742choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r742targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)] c8r742choice = true := by decide
    refine ⟨c8r742targets, c8r742choice, ?_, checked⟩
    intro S h
    simp only [c8r742targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L23_lift _ (familyLookup_sound F9B002L23 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 3 _ (by rfl)))
  have c8r743_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)] := by
    let c8r743targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)]]
    let c8r743choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r743targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)] c8r743choice = true := by decide
    refine ⟨c8r743targets, c8r743choice, ?_, checked⟩
    intro S h
    simp only [c8r743targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 6 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r736_closed
  · subst row; exact c8r737_closed
  · subst row; exact c8r738_closed
  · subst row; exact c8r739_closed
  · subst row; exact c8r740_closed
  · subst row; exact c8r741_closed
  · subst row; exact c8r742_closed
  · subst row; exact c8r743_closed
theorem C8R00736G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r744_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)] := by
    let c8r744targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)]]
    let c8r744choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r744targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)] c8r744choice = true := by decide
    refine ⟨c8r744targets, c8r744choice, ?_, checked⟩
    intro S h
    simp only [c8r744targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 8 _ (by rfl)))
  have c8r745_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)] := by
    let c8r745targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
    let c8r745choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r745targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)] c8r745choice = true := by decide
    refine ⟨c8r745targets, c8r745choice, ?_, checked⟩
    intro S h
    simp only [c8r745targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 11 _ (by rfl)))
  have c8r746_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)] := by
    let c8r746targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)]]
    let c8r746choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r746targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)] c8r746choice = true := by decide
    refine ⟨c8r746targets, c8r746choice, ?_, checked⟩
    intro S h
    simp only [c8r746targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 14 _ (by rfl)))
  have c8r747_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)] := by
    let c8r747targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)]]
    let c8r747choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r747targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)] c8r747choice = true := by decide
    refine ⟨c8r747targets, c8r747choice, ?_, checked⟩
    intro S h
    simp only [c8r747targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 17 _ (by rfl)))
  have c8r748_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)] := by
    let c8r748targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)]]
    let c8r748choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,5),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r748targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)] c8r748choice = true := by decide
    refine ⟨c8r748targets, c8r748choice, ?_, checked⟩
    intro S h
    simp only [c8r748targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 21 _ (by rfl)))
  have c8r749_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)] := by
    let c8r749targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)]]
    let c8r749choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r749targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)] c8r749choice = true := by decide
    refine ⟨c8r749targets, c8r749choice, ?_, checked⟩
    intro S h
    simp only [c8r749targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 24 _ (by rfl)))
  have c8r750_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)] := by
    let c8r750targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)]]
    let c8r750choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r750targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)] c8r750choice = true := by decide
    refine ⟨c8r750targets, c8r750choice, ?_, checked⟩
    intro S h
    simp only [c8r750targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 26 _ (by rfl)))
  have c8r751_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)] := by
    let c8r751targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)]]
    let c8r751choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r751targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)] c8r751choice = true := by decide
    refine ⟨c8r751targets, c8r751choice, ?_, checked⟩
    intro S h
    simp only [c8r751targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 30 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r744_closed
  · subst row; exact c8r745_closed
  · subst row; exact c8r746_closed
  · subst row; exact c8r747_closed
  · subst row; exact c8r748_closed
  · subst row; exact c8r749_closed
  · subst row; exact c8r750_closed
  · subst row; exact c8r751_closed
theorem C8R00736G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r752_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)] := by
    let c8r752targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)]]
    let c8r752choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r752targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)] c8r752choice = true := by decide
    refine ⟨c8r752targets, c8r752choice, ?_, checked⟩
    intro S h
    simp only [c8r752targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 1 _ (by rfl)))
  have c8r753_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)] := by
    let c8r753targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)]]
    let c8r753choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r753targets [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)] c8r753choice = true := by decide
    refine ⟨c8r753targets, c8r753choice, ?_, checked⟩
    intro S h
    simp only [c8r753targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 4 _ (by rfl)))
  have c8r754_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c8r754targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c8r754choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r754targets [(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] c8r754choice = true := by decide
    refine ⟨c8r754targets, c8r754choice, ?_, checked⟩
    intro S h
    simp only [c8r754targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 9 _ (by rfl)))
  have c8r755_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r755targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r755choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r755targets [(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)] c8r755choice = true := by decide
    refine ⟨c8r755targets, c8r755choice, ?_, checked⟩
    intro S h
    simp only [c8r755targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 14 _ (by rfl)))
  have c8r756_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r756targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r756choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r756targets [(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)] c8r756choice = true := by decide
    refine ⟨c8r756targets, c8r756choice, ?_, checked⟩
    intro S h
    simp only [c8r756targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 17 _ (by rfl)))
  have c8r757_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r757targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r757choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r757targets [(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)] c8r757choice = true := by decide
    refine ⟨c8r757targets, c8r757choice, ?_, checked⟩
    intro S h
    simp only [c8r757targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 19 _ (by rfl)))
  have c8r758_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r758targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r758choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r758targets [(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)] c8r758choice = true := by decide
    refine ⟨c8r758targets, c8r758choice, ?_, checked⟩
    intro S h
    simp only [c8r758targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L24_lift _ (familyLookup_sound F9B002L24 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 21 _ (by rfl)))
  have c8r759_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)] := by
    let c8r759targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,5),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3)]]
    let c8r759choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((-1,5),(3,(1,0))),((0,-1),(4,(0,1))),((0,1),(5,(0,0))),((0,2),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,4),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,1),(12,(0,0))),((2,2),(13,(0,0))),((2,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r759targets [(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)] c8r759choice = true := by decide
    refine ⟨c8r759targets, c8r759choice, ?_, checked⟩
    intro S h
    simp only [c8r759targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 0 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 26 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 3 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 29 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r752_closed
  · subst row; exact c8r753_closed
  · subst row; exact c8r754_closed
  · subst row; exact c8r755_closed
  · subst row; exact c8r756_closed
  · subst row; exact c8r757_closed
  · subst row; exact c8r758_closed
  · subst row; exact c8r759_closed
theorem C8R00736G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r760_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r760targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r760choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,2),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r760targets [(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)] c8r760choice = true := by decide
    refine ⟨c8r760targets, c8r760choice, ?_, checked⟩
    intro S h
    simp only [c8r760targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 1 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 27 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 3 _ (by rfl)))
  have c8r761_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)] := by
    let c8r761targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
    let c8r761choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,2),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((3,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r761targets [(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)] c8r761choice = true := by decide
    refine ⟨c8r761targets, c8r761choice, ?_, checked⟩
    intro S h
    simp only [c8r761targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 2 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 28 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 7 _ (by rfl)))
  have c8r762_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)] := by
    let c8r762targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
    let c8r762choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,2),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r762targets [(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)] c8r762choice = true := by decide
    refine ⟨c8r762targets, c8r762choice, ?_, checked⟩
    intro S h
    simp only [c8r762targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 3 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 29 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 10 _ (by rfl)))
  have c8r763_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)] := by
    let c8r763targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
    let c8r763choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,2),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r763targets [(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)] c8r763choice = true := by decide
    refine ⟨c8r763targets, c8r763choice, ?_, checked⟩
    intro S h
    simp only [c8r763targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 4 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 30 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 12 _ (by rfl)))
  have c8r764_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)] := by
    let c8r764targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
    let c8r764choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,2),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r764targets [(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)] c8r764choice = true := by decide
    refine ⟨c8r764targets, c8r764choice, ?_, checked⟩
    intro S h
    simp only [c8r764targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 5 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 31 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 14 _ (by rfl)))
  have c8r765_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r765targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r765choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r765targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r765choice = true := by decide
    refine ⟨c8r765targets, c8r765choice, ?_, checked⟩
    intro S h
    simp only [c8r765targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 6 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 25 _ (by rfl)))
  have c8r766_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] := by
    let c8r766targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
    let c8r766choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r766targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] c8r766choice = true := by decide
    refine ⟨c8r766targets, c8r766choice, ?_, checked⟩
    intro S h
    simp only [c8r766targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 7 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 30 _ (by rfl)))
  have c8r767_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c8r767targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c8r767choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r767targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] c8r767choice = true := by decide
    refine ⟨c8r767targets, c8r767choice, ?_, checked⟩
    intro S h
    simp only [c8r767targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 8 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 2 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r760_closed
  · subst row; exact c8r761_closed
  · subst row; exact c8r762_closed
  · subst row; exact c8r763_closed
  · subst row; exact c8r764_closed
  · subst row; exact c8r765_closed
  · subst row; exact c8r766_closed
  · subst row; exact c8r767_closed
theorem C8R00736_closed (row : List GridPoint) (h : FamilyMember row F8B000L23) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L23, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00736G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00736G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00736G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00736G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00736G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00736G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00736G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00736G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00736G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00736G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00736G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00736G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00736G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00736G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00736G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00736G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00736G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00736G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00736G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00736G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00736G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00736G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00736G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00736G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00736G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00736G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00736G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00736G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00736G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00736G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00736G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00736G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
