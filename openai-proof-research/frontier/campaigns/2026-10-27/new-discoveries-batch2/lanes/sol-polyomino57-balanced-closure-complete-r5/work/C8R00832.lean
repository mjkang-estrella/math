import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00832G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r832_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)] := by
    let c8r832targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)]]
    let c8r832choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r832targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)] c8r832choice = true := by decide
    refine ⟨c8r832targets, c8r832choice, ?_, checked⟩
    intro S h
    simp only [c8r832targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 16 _ (by rfl)))
  have c8r833_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)] := by
    let c8r833targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)]]
    let c8r833choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r833targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)] c8r833choice = true := by decide
    refine ⟨c8r833targets, c8r833choice, ?_, checked⟩
    intro S h
    simp only [c8r833targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 19 _ (by rfl)))
  have c8r834_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)] := by
    let c8r834targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)]]
    let c8r834choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r834targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)] c8r834choice = true := by decide
    refine ⟨c8r834targets, c8r834choice, ?_, checked⟩
    intro S h
    simp only [c8r834targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 22 _ (by rfl)))
  have c8r835_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)] := by
    let c8r835targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)]]
    let c8r835choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r835targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)] c8r835choice = true := by decide
    refine ⟨c8r835targets, c8r835choice, ?_, checked⟩
    intro S h
    simp only [c8r835targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 25 _ (by rfl)))
  have c8r836_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)] := by
    let c8r836targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)]]
    let c8r836choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r836targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)] c8r836choice = true := by decide
    refine ⟨c8r836targets, c8r836choice, ?_, checked⟩
    intro S h
    simp only [c8r836targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 28 _ (by rfl)))
  have c8r837_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)] := by
    let c8r837targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)]]
    let c8r837choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r837targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)] c8r837choice = true := by decide
    refine ⟨c8r837targets, c8r837choice, ?_, checked⟩
    intro S h
    simp only [c8r837targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 0 _ (by rfl)))
  have c8r838_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)] := by
    let c8r838targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)]]
    let c8r838choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r838targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)] c8r838choice = true := by decide
    refine ⟨c8r838targets, c8r838choice, ?_, checked⟩
    intro S h
    simp only [c8r838targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 3 _ (by rfl)))
  have c8r839_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)] := by
    let c8r839targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)]]
    let c8r839choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r839targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)] c8r839choice = true := by decide
    refine ⟨c8r839targets, c8r839choice, ?_, checked⟩
    intro S h
    simp only [c8r839targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 5 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r832_closed
  · subst row; exact c8r833_closed
  · subst row; exact c8r834_closed
  · subst row; exact c8r835_closed
  · subst row; exact c8r836_closed
  · subst row; exact c8r837_closed
  · subst row; exact c8r838_closed
  · subst row; exact c8r839_closed
theorem C8R00832G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r840_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)] := by
    let c8r840targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)]]
    let c8r840choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r840targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)] c8r840choice = true := by decide
    refine ⟨c8r840targets, c8r840choice, ?_, checked⟩
    intro S h
    simp only [c8r840targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 9 _ (by rfl)))
  have c8r841_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)] := by
    let c8r841targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)]]
    let c8r841choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r841targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)] c8r841choice = true := by decide
    refine ⟨c8r841targets, c8r841choice, ?_, checked⟩
    intro S h
    simp only [c8r841targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 12 _ (by rfl)))
  have c8r842_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)] := by
    let c8r842targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)]]
    let c8r842choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r842targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)] c8r842choice = true := by decide
    refine ⟨c8r842targets, c8r842choice, ?_, checked⟩
    intro S h
    simp only [c8r842targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 15 _ (by rfl)))
  have c8r843_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)] := by
    let c8r843targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)]]
    let c8r843choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,6),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r843targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)] c8r843choice = true := by decide
    refine ⟨c8r843targets, c8r843choice, ?_, checked⟩
    intro S h
    simp only [c8r843targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 19 _ (by rfl)))
  have c8r844_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)] := by
    let c8r844targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)]]
    let c8r844choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r844targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)] c8r844choice = true := by decide
    refine ⟨c8r844targets, c8r844choice, ?_, checked⟩
    intro S h
    simp only [c8r844targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 22 _ (by rfl)))
  have c8r845_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)] := by
    let c8r845targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)]]
    let c8r845choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,3),(11,(0,0))),((3,5),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r845targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)] c8r845choice = true := by decide
    refine ⟨c8r845targets, c8r845choice, ?_, checked⟩
    intro S h
    simp only [c8r845targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 24 _ (by rfl)))
  have c8r846_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)] := by
    let c8r846targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)]]
    let c8r846choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r846targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)] c8r846choice = true := by decide
    refine ⟨c8r846targets, c8r846choice, ?_, checked⟩
    intro S h
    simp only [c8r846targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 28 _ (by rfl)))
  have c8r847_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)] := by
    let c8r847targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)]]
    let c8r847choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,5),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r847targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)] c8r847choice = true := by decide
    refine ⟨c8r847targets, c8r847choice, ?_, checked⟩
    intro S h
    simp only [c8r847targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 31 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r840_closed
  · subst row; exact c8r841_closed
  · subst row; exact c8r842_closed
  · subst row; exact c8r843_closed
  · subst row; exact c8r844_closed
  · subst row; exact c8r845_closed
  · subst row; exact c8r846_closed
  · subst row; exact c8r847_closed
theorem C8R00832G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r848_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)] := by
    let c8r848targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)]]
    let c8r848choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0))),((4,4),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r848targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)] c8r848choice = true := by decide
    refine ⟨c8r848targets, c8r848choice, ?_, checked⟩
    intro S h
    simp only [c8r848targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 2 _ (by rfl)))
  have c8r849_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)] := by
    let c8r849targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)]]
    let c8r849choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,5),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r849targets [(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)] c8r849choice = true := by decide
    refine ⟨c8r849targets, c8r849choice, ?_, checked⟩
    intro S h
    simp only [c8r849targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 9 _ (by rfl)))
  have c8r850_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r850targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r850choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r850targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)] c8r850choice = true := by decide
    refine ⟨c8r850targets, c8r850choice, ?_, checked⟩
    intro S h
    simp only [c8r850targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 15 _ (by rfl)))
  have c8r851_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r851targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r851choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r851targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)] c8r851choice = true := by decide
    refine ⟨c8r851targets, c8r851choice, ?_, checked⟩
    intro S h
    simp only [c8r851targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 18 _ (by rfl)))
  have c8r852_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r852targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r852choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r852targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)] c8r852choice = true := by decide
    refine ⟨c8r852targets, c8r852choice, ?_, checked⟩
    intro S h
    simp only [c8r852targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 20 _ (by rfl)))
  have c8r853_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r853targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r853choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r853targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)] c8r853choice = true := by decide
    refine ⟨c8r853targets, c8r853choice, ?_, checked⟩
    intro S h
    simp only [c8r853targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 22 _ (by rfl)))
  have c8r854_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)] := by
    let c8r854targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c8r854choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r854targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)] c8r854choice = true := by decide
    refine ⟨c8r854targets, c8r854choice, ?_, checked⟩
    intro S h
    simp only [c8r854targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 25 _ (by rfl)))
  have c8r855_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)] := by
    let c8r855targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c8r855choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r855targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)] c8r855choice = true := by decide
    refine ⟨c8r855targets, c8r855choice, ?_, checked⟩
    intro S h
    simp only [c8r855targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 27 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r848_closed
  · subst row; exact c8r849_closed
  · subst row; exact c8r850_closed
  · subst row; exact c8r851_closed
  · subst row; exact c8r852_closed
  · subst row; exact c8r853_closed
  · subst row; exact c8r854_closed
  · subst row; exact c8r855_closed
theorem C8R00832G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r856_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)] := by
    let c8r856targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c8r856choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r856targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)] c8r856choice = true := by decide
    refine ⟨c8r856targets, c8r856choice, ?_, checked⟩
    intro S h
    simp only [c8r856targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 30 _ (by rfl)))
  have c8r857_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)] := by
    let c8r857targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c8r857choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r857targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)] c8r857choice = true := by decide
    refine ⟨c8r857targets, c8r857choice, ?_, checked⟩
    intro S h
    simp only [c8r857targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 1 _ (by rfl)))
  have c8r858_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)] := by
    let c8r858targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)]]
    let c8r858choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r858targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)] c8r858choice = true := by decide
    refine ⟨c8r858targets, c8r858choice, ?_, checked⟩
    intro S h
    simp only [c8r858targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 6 _ (by rfl)))
  have c8r859_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)] := by
    let c8r859targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(4,0)]]
    let c8r859choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r859targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)] c8r859choice = true := by decide
    refine ⟨c8r859targets, c8r859choice, ?_, checked⟩
    intro S h
    simp only [c8r859targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 10 _ (by rfl)))
  have c8r860_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)] := by
    let c8r860targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2)]]
    let c8r860choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r860targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)] c8r860choice = true := by decide
    refine ⟨c8r860targets, c8r860choice, ?_, checked⟩
    intro S h
    simp only [c8r860targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 13 _ (by rfl)))
  have c8r861_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)] := by
    let c8r861targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3)]]
    let c8r861choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r861targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)] c8r861choice = true := by decide
    refine ⟨c8r861targets, c8r861choice, ?_, checked⟩
    intro S h
    simp only [c8r861targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 15 _ (by rfl)))
  have c8r862_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)] := by
    let c8r862targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,1)]]
    let c8r862choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r862targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)] c8r862choice = true := by decide
    refine ⟨c8r862targets, c8r862choice, ?_, checked⟩
    intro S h
    simp only [c8r862targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 18 _ (by rfl)))
  have c8r863_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)] := by
    let c8r863targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,2)]]
    let c8r863choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r863targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)] c8r863choice = true := by decide
    refine ⟨c8r863targets, c8r863choice, ?_, checked⟩
    intro S h
    simp only [c8r863targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 21 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r856_closed
  · subst row; exact c8r857_closed
  · subst row; exact c8r858_closed
  · subst row; exact c8r859_closed
  · subst row; exact c8r860_closed
  · subst row; exact c8r861_closed
  · subst row; exact c8r862_closed
  · subst row; exact c8r863_closed
theorem C8R00832_closed (row : List GridPoint) (h : FamilyMember row F8B000L26) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L26, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00832G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00832G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00832G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00832G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00832G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00832G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00832G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00832G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00832G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00832G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00832G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00832G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00832G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00832G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00832G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00832G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00832G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00832G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00832G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00832G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00832G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00832G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00832G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00832G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00832G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00832G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00832G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00832G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00832G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00832G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00832G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00832G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
