import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00480G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r480_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c8r480targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c8r480choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r480targets [(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] c8r480choice = true := by decide
    refine ⟨c8r480targets, c8r480choice, ?_, checked⟩
    intro S h
    simp only [c8r480targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 7 _ (by rfl)))
  have c8r481_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r481targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r481choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r481targets [(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)] c8r481choice = true := by decide
    refine ⟨c8r481targets, c8r481choice, ?_, checked⟩
    intro S h
    simp only [c8r481targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 12 _ (by rfl)))
  have c8r482_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r482targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r482choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r482targets [(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)] c8r482choice = true := by decide
    refine ⟨c8r482targets, c8r482choice, ?_, checked⟩
    intro S h
    simp only [c8r482targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 15 _ (by rfl)))
  have c8r483_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r483targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r483choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r483targets [(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)] c8r483choice = true := by decide
    refine ⟨c8r483targets, c8r483choice, ?_, checked⟩
    intro S h
    simp only [c8r483targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 17 _ (by rfl)))
  have c8r484_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r484targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r484choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r484targets [(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)] c8r484choice = true := by decide
    refine ⟨c8r484targets, c8r484choice, ?_, checked⟩
    intro S h
    simp only [c8r484targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 19 _ (by rfl)))
  have c8r485_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r485targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r485choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r485targets [(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)] c8r485choice = true := by decide
    refine ⟨c8r485targets, c8r485choice, ?_, checked⟩
    intro S h
    simp only [c8r485targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 26 _ (by rfl)))
  have c8r486_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r486targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r486choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,5),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r486targets [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)] c8r486choice = true := by decide
    refine ⟨c8r486targets, c8r486choice, ?_, checked⟩
    intro S h
    simp only [c8r486targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 1 _ (by rfl)))
  have c8r487_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c8r487targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c8r487choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r487targets [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)] c8r487choice = true := by decide
    refine ⟨c8r487targets, c8r487choice, ?_, checked⟩
    intro S h
    simp only [c8r487targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 5 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r480_closed
  · subst row; exact c8r481_closed
  · subst row; exact c8r482_closed
  · subst row; exact c8r483_closed
  · subst row; exact c8r484_closed
  · subst row; exact c8r485_closed
  · subst row; exact c8r486_closed
  · subst row; exact c8r487_closed
theorem C8R00480G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r488_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r488targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r488choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r488targets [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)] c8r488choice = true := by decide
    refine ⟨c8r488targets, c8r488choice, ?_, checked⟩
    intro S h
    simp only [c8r488targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 8 _ (by rfl)))
  have c8r489_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r489targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r489choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r489targets [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)] c8r489choice = true := by decide
    refine ⟨c8r489targets, c8r489choice, ?_, checked⟩
    intro S h
    simp only [c8r489targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 10 _ (by rfl)))
  have c8r490_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r490targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r490choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r490targets [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3)] c8r490choice = true := by decide
    refine ⟨c8r490targets, c8r490choice, ?_, checked⟩
    intro S h
    simp only [c8r490targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 12 _ (by rfl)))
  have c8r491_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r491targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r491choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r491targets [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)] c8r491choice = true := by decide
    refine ⟨c8r491targets, c8r491choice, ?_, checked⟩
    intro S h
    simp only [c8r491targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 15 _ (by rfl)))
  have c8r492_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c8r492targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c8r492choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r492targets [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)] c8r492choice = true := by decide
    refine ⟨c8r492targets, c8r492choice, ?_, checked⟩
    intro S h
    simp only [c8r492targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 18 _ (by rfl)))
  have c8r493_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c8r493targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c8r493choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r493targets [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)] c8r493choice = true := by decide
    refine ⟨c8r493targets, c8r493choice, ?_, checked⟩
    intro S h
    simp only [c8r493targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 20 _ (by rfl)))
  have c8r494_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c8r494targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c8r494choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r494targets [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)] c8r494choice = true := by decide
    refine ⟨c8r494targets, c8r494choice, ?_, checked⟩
    intro S h
    simp only [c8r494targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 23 _ (by rfl)))
  have c8r495_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c8r495targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c8r495choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r495targets [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)] c8r495choice = true := by decide
    refine ⟨c8r495targets, c8r495choice, ?_, checked⟩
    intro S h
    simp only [c8r495targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 26 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r488_closed
  · subst row; exact c8r489_closed
  · subst row; exact c8r490_closed
  · subst row; exact c8r491_closed
  · subst row; exact c8r492_closed
  · subst row; exact c8r493_closed
  · subst row; exact c8r494_closed
  · subst row; exact c8r495_closed
theorem C8R00480G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r496_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c8r496targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c8r496choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r496targets [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3)] c8r496choice = true := by decide
    refine ⟨c8r496targets, c8r496choice, ?_, checked⟩
    intro S h
    simp only [c8r496targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 29 _ (by rfl)))
  have c8r497_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2)] := by
    let c8r497targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c8r497choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r497targets [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2)] c8r497choice = true := by decide
    refine ⟨c8r497targets, c8r497choice, ?_, checked⟩
    intro S h
    simp only [c8r497targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 0 _ (by rfl)))
  have c8r498_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)] := by
    let c8r498targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c8r498choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r498targets [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)] c8r498choice = true := by decide
    refine ⟨c8r498targets, c8r498choice, ?_, checked⟩
    intro S h
    simp only [c8r498targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 5 _ (by rfl)))
  have c8r499_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)] := by
    let c8r499targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c8r499choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r499targets [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)] c8r499choice = true := by decide
    refine ⟨c8r499targets, c8r499choice, ?_, checked⟩
    intro S h
    simp only [c8r499targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 7 _ (by rfl)))
  have c8r500_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)] := by
    let c8r500targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c8r500choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r500targets [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)] c8r500choice = true := by decide
    refine ⟨c8r500targets, c8r500choice, ?_, checked⟩
    intro S h
    simp only [c8r500targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 9 _ (by rfl)))
  have c8r501_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)] := by
    let c8r501targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)]]
    let c8r501choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r501targets [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)] c8r501choice = true := by decide
    refine ⟨c8r501targets, c8r501choice, ?_, checked⟩
    intro S h
    simp only [c8r501targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 12 _ (by rfl)))
  have c8r502_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)] := by
    let c8r502targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)]]
    let c8r502choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r502targets [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)] c8r502choice = true := by decide
    refine ⟨c8r502targets, c8r502choice, ?_, checked⟩
    intro S h
    simp only [c8r502targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 14 _ (by rfl)))
  have c8r503_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3)] := by
    let c8r503targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c8r503choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r503targets [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3)] c8r503choice = true := by decide
    refine ⟨c8r503targets, c8r503choice, ?_, checked⟩
    intro S h
    simp only [c8r503targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 18 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r496_closed
  · subst row; exact c8r497_closed
  · subst row; exact c8r498_closed
  · subst row; exact c8r499_closed
  · subst row; exact c8r500_closed
  · subst row; exact c8r501_closed
  · subst row; exact c8r502_closed
  · subst row; exact c8r503_closed
theorem C8R00480G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r504_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)] := by
    let c8r504targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c8r504choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r504targets [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)] c8r504choice = true := by decide
    refine ⟨c8r504targets, c8r504choice, ?_, checked⟩
    intro S h
    simp only [c8r504targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 21 _ (by rfl)))
  have c8r505_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2)] := by
    let c8r505targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c8r505choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r505targets [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2)] c8r505choice = true := by decide
    refine ⟨c8r505targets, c8r505choice, ?_, checked⟩
    intro S h
    simp only [c8r505targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 23 _ (by rfl)))
  have c8r506_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1)] := by
    let c8r506targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c8r506choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r506targets [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1)] c8r506choice = true := by decide
    refine ⟨c8r506targets, c8r506choice, ?_, checked⟩
    intro S h
    simp only [c8r506targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 26 _ (by rfl)))
  have c8r507_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2)] := by
    let c8r507targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c8r507choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r507targets [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2)] c8r507choice = true := by decide
    refine ⟨c8r507targets, c8r507choice, ?_, checked⟩
    intro S h
    simp only [c8r507targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 29 _ (by rfl)))
  have c8r508_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1)] := by
    let c8r508targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c8r508choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r508targets [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1)] c8r508choice = true := by decide
    refine ⟨c8r508targets, c8r508choice, ?_, checked⟩
    intro S h
    simp only [c8r508targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 0 _ (by rfl)))
  have c8r509_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r509targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r509choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r509targets [(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2)] c8r509choice = true := by decide
    refine ⟨c8r509targets, c8r509choice, ?_, checked⟩
    intro S h
    simp only [c8r509targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L14_lift _ (familyLookup_sound F9B002L14 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 5 _ (by rfl)))
  have c8r510_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r510targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r510choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r510targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3)] c8r510choice = true := by decide
    refine ⟨c8r510targets, c8r510choice, ?_, checked⟩
    intro S h
    simp only [c8r510targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 11 _ (by rfl)))
  have c8r511_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r511targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r511choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r511targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)] c8r511choice = true := by decide
    refine ⟨c8r511targets, c8r511choice, ?_, checked⟩
    intro S h
    simp only [c8r511targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 14 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r504_closed
  · subst row; exact c8r505_closed
  · subst row; exact c8r506_closed
  · subst row; exact c8r507_closed
  · subst row; exact c8r508_closed
  · subst row; exact c8r509_closed
  · subst row; exact c8r510_closed
  · subst row; exact c8r511_closed
theorem C8R00480_closed (row : List GridPoint) (h : FamilyMember row F8B000L15) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L15, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00480G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00480G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00480G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00480G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00480G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00480G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00480G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00480G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00480G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00480G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00480G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00480G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00480G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00480G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00480G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00480G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00480G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00480G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00480G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00480G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00480G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00480G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00480G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00480G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00480G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00480G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00480G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00480G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00480G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00480G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00480G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00480G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
