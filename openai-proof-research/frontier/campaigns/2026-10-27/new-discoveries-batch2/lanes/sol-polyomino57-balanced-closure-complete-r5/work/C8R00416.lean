import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00416G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r416_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r416targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r416choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r416targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] c8r416choice = true := by decide
    refine ⟨c8r416targets, c8r416choice, ?_, checked⟩
    intro S h
    simp only [c8r416targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 1 _ (by rfl)))
  have c8r417_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c8r417targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c8r417choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r417targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] c8r417choice = true := by decide
    refine ⟨c8r417targets, c8r417choice, ?_, checked⟩
    intro S h
    simp only [c8r417targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 5 _ (by rfl)))
  have c8r418_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] := by
    let c8r418targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)]]
    let c8r418choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r418targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] c8r418choice = true := by decide
    refine ⟨c8r418targets, c8r418choice, ?_, checked⟩
    intro S h
    simp only [c8r418targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 8 _ (by rfl)))
  have c8r419_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] := by
    let c8r419targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)]]
    let c8r419choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r419targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] c8r419choice = true := by decide
    refine ⟨c8r419targets, c8r419choice, ?_, checked⟩
    intro S h
    simp only [c8r419targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 11 _ (by rfl)))
  have c8r420_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] := by
    let c8r420targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)]]
    let c8r420choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r420targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] c8r420choice = true := by decide
    refine ⟨c8r420targets, c8r420choice, ?_, checked⟩
    intro S h
    simp only [c8r420targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 13 _ (by rfl)))
  have c8r421_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] := by
    let c8r421targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
    let c8r421choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r421targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] c8r421choice = true := by decide
    refine ⟨c8r421targets, c8r421choice, ?_, checked⟩
    intro S h
    simp only [c8r421targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 16 _ (by rfl)))
  have c8r422_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] := by
    let c8r422targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
    let c8r422choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r422targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] c8r422choice = true := by decide
    refine ⟨c8r422targets, c8r422choice, ?_, checked⟩
    intro S h
    simp only [c8r422targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 19 _ (by rfl)))
  have c8r423_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] := by
    let c8r423targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
    let c8r423choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r423targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] c8r423choice = true := by decide
    refine ⟨c8r423targets, c8r423choice, ?_, checked⟩
    intro S h
    simp only [c8r423targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 22 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r416_closed
  · subst row; exact c8r417_closed
  · subst row; exact c8r418_closed
  · subst row; exact c8r419_closed
  · subst row; exact c8r420_closed
  · subst row; exact c8r421_closed
  · subst row; exact c8r422_closed
  · subst row; exact c8r423_closed
theorem C8R00416G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r424_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] := by
    let c8r424targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
    let c8r424choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r424targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] c8r424choice = true := by decide
    refine ⟨c8r424targets, c8r424choice, ?_, checked⟩
    intro S h
    simp only [c8r424targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 25 _ (by rfl)))
  have c8r425_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] := by
    let c8r425targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
    let c8r425choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r425targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] c8r425choice = true := by decide
    refine ⟨c8r425targets, c8r425choice, ?_, checked⟩
    intro S h
    simp only [c8r425targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 28 _ (by rfl)))
  have c8r426_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)] := by
    let c8r426targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
    let c8r426choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r426targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)] c8r426choice = true := by decide
    refine ⟨c8r426targets, c8r426choice, ?_, checked⟩
    intro S h
    simp only [c8r426targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 31 _ (by rfl)))
  have c8r427_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)] := by
    let c8r427targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
    let c8r427choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r427targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)] c8r427choice = true := by decide
    refine ⟨c8r427targets, c8r427choice, ?_, checked⟩
    intro S h
    simp only [c8r427targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 2 _ (by rfl)))
  have c8r428_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)] := by
    let c8r428targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]
    let c8r428choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r428targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)] c8r428choice = true := by decide
    refine ⟨c8r428targets, c8r428choice, ?_, checked⟩
    intro S h
    simp only [c8r428targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 7 _ (by rfl)))
  have c8r429_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)] := by
    let c8r429targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]
    let c8r429choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r429targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)] c8r429choice = true := by decide
    refine ⟨c8r429targets, c8r429choice, ?_, checked⟩
    intro S h
    simp only [c8r429targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 9 _ (by rfl)))
  have c8r430_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)] := by
    let c8r430targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
    let c8r430choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r430targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)] c8r430choice = true := by decide
    refine ⟨c8r430targets, c8r430choice, ?_, checked⟩
    intro S h
    simp only [c8r430targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 11 _ (by rfl)))
  have c8r431_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)] := by
    let c8r431targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)]]
    let c8r431choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r431targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)] c8r431choice = true := by decide
    refine ⟨c8r431targets, c8r431choice, ?_, checked⟩
    intro S h
    simp only [c8r431targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 15 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r424_closed
  · subst row; exact c8r425_closed
  · subst row; exact c8r426_closed
  · subst row; exact c8r427_closed
  · subst row; exact c8r428_closed
  · subst row; exact c8r429_closed
  · subst row; exact c8r430_closed
  · subst row; exact c8r431_closed
theorem C8R00416G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r432_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)] := by
    let c8r432targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)]]
    let c8r432choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r432targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)] c8r432choice = true := by decide
    refine ⟨c8r432targets, c8r432choice, ?_, checked⟩
    intro S h
    simp only [c8r432targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 18 _ (by rfl)))
  have c8r433_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)] := by
    let c8r433targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)]]
    let c8r433choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r433targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)] c8r433choice = true := by decide
    refine ⟨c8r433targets, c8r433choice, ?_, checked⟩
    intro S h
    simp only [c8r433targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 21 _ (by rfl)))
  have c8r434_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)] := by
    let c8r434targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)]]
    let c8r434choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r434targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)] c8r434choice = true := by decide
    refine ⟨c8r434targets, c8r434choice, ?_, checked⟩
    intro S h
    simp only [c8r434targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 24 _ (by rfl)))
  have c8r435_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)] := by
    let c8r435targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)]]
    let c8r435choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r435targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)] c8r435choice = true := by decide
    refine ⟨c8r435targets, c8r435choice, ?_, checked⟩
    intro S h
    simp only [c8r435targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 26 _ (by rfl)))
  have c8r436_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)] := by
    let c8r436targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)]]
    let c8r436choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r436targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)] c8r436choice = true := by decide
    refine ⟨c8r436targets, c8r436choice, ?_, checked⟩
    intro S h
    simp only [c8r436targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 30 _ (by rfl)))
  have c8r437_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)] := by
    let c8r437targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)]]
    let c8r437choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r437targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)] c8r437choice = true := by decide
    refine ⟨c8r437targets, c8r437choice, ?_, checked⟩
    intro S h
    simp only [c8r437targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 1 _ (by rfl)))
  have c8r438_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)] := by
    let c8r438targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)]]
    let c8r438choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r438targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)] c8r438choice = true := by decide
    refine ⟨c8r438targets, c8r438choice, ?_, checked⟩
    intro S h
    simp only [c8r438targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 3 _ (by rfl)))
  have c8r439_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)] := by
    let c8r439targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
    let c8r439choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r439targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)] c8r439choice = true := by decide
    refine ⟨c8r439targets, c8r439choice, ?_, checked⟩
    intro S h
    simp only [c8r439targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 6 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r432_closed
  · subst row; exact c8r433_closed
  · subst row; exact c8r434_closed
  · subst row; exact c8r435_closed
  · subst row; exact c8r436_closed
  · subst row; exact c8r437_closed
  · subst row; exact c8r438_closed
  · subst row; exact c8r439_closed
theorem C8R00416G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r440_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)] := by
    let c8r440targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)]]
    let c8r440choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r440targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)] c8r440choice = true := by decide
    refine ⟨c8r440targets, c8r440choice, ?_, checked⟩
    intro S h
    simp only [c8r440targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 9 _ (by rfl)))
  have c8r441_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)] := by
    let c8r441targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)]]
    let c8r441choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r441targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)] c8r441choice = true := by decide
    refine ⟨c8r441targets, c8r441choice, ?_, checked⟩
    intro S h
    simp only [c8r441targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 12 _ (by rfl)))
  have c8r442_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)] := by
    let c8r442targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)]]
    let c8r442choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r442targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)] c8r442choice = true := by decide
    refine ⟨c8r442targets, c8r442choice, ?_, checked⟩
    intro S h
    simp only [c8r442targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 16 _ (by rfl)))
  have c8r443_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)] := by
    let c8r443targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)]]
    let c8r443choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r443targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)] c8r443choice = true := by decide
    refine ⟨c8r443targets, c8r443choice, ?_, checked⟩
    intro S h
    simp only [c8r443targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 19 _ (by rfl)))
  have c8r444_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)] := by
    let c8r444targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)]]
    let c8r444choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r444targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)] c8r444choice = true := by decide
    refine ⟨c8r444targets, c8r444choice, ?_, checked⟩
    intro S h
    simp only [c8r444targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 21 _ (by rfl)))
  have c8r445_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)] := by
    let c8r445targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)]]
    let c8r445choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r445targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)] c8r445choice = true := by decide
    refine ⟨c8r445targets, c8r445choice, ?_, checked⟩
    intro S h
    simp only [c8r445targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 25 _ (by rfl)))
  have c8r446_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)] := by
    let c8r446targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)]]
    let c8r446choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r446targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)] c8r446choice = true := by decide
    refine ⟨c8r446targets, c8r446choice, ?_, checked⟩
    intro S h
    simp only [c8r446targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 28 _ (by rfl)))
  have c8r447_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)] := by
    let c8r447targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)]]
    let c8r447choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r447targets [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)] c8r447choice = true := by decide
    refine ⟨c8r447targets, c8r447choice, ?_, checked⟩
    intro S h
    simp only [c8r447targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 31 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r440_closed
  · subst row; exact c8r441_closed
  · subst row; exact c8r442_closed
  · subst row; exact c8r443_closed
  · subst row; exact c8r444_closed
  · subst row; exact c8r445_closed
  · subst row; exact c8r446_closed
  · subst row; exact c8r447_closed
theorem C8R00416_closed (row : List GridPoint) (h : FamilyMember row F8B000L13) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L13, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00416G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00416G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00416G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00416G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00416G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00416G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00416G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00416G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00416G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00416G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00416G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00416G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00416G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00416G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00416G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00416G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00416G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00416G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00416G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00416G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00416G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00416G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00416G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00416G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00416G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00416G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00416G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00416G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00416G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00416G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00416G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00416G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
