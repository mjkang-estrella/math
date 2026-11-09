import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00800G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r800_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] := by
    let c8r800targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
    let c8r800choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r800targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] c8r800choice = true := by decide
    refine ⟨c8r800targets, c8r800choice, ?_, checked⟩
    intro S h
    simp only [c8r800targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 11 _ (by rfl)))
  have c8r801_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)] := by
    let c8r801targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)]]
    let c8r801choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r801targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)] c8r801choice = true := by decide
    refine ⟨c8r801targets, c8r801choice, ?_, checked⟩
    intro S h
    simp only [c8r801targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 15 _ (by rfl)))
  have c8r802_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)] := by
    let c8r802targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)]]
    let c8r802choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r802targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)] c8r802choice = true := by decide
    refine ⟨c8r802targets, c8r802choice, ?_, checked⟩
    intro S h
    simp only [c8r802targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 18 _ (by rfl)))
  have c8r803_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)] := by
    let c8r803targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)]]
    let c8r803choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,0),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r803targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)] c8r803choice = true := by decide
    refine ⟨c8r803targets, c8r803choice, ?_, checked⟩
    intro S h
    simp only [c8r803targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 21 _ (by rfl)))
  have c8r804_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)] := by
    let c8r804targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)]]
    let c8r804choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,-1),(13,(0,1))),((3,1),(14,(0,0))),((4,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r804targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)] c8r804choice = true := by decide
    refine ⟨c8r804targets, c8r804choice, ?_, checked⟩
    intro S h
    simp only [c8r804targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 23 _ (by rfl)))
  have c8r805_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)] := by
    let c8r805targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)]]
    let c8r805choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r805targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)] c8r805choice = true := by decide
    refine ⟨c8r805targets, c8r805choice, ?_, checked⟩
    intro S h
    simp only [c8r805targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 27 _ (by rfl)))
  have c8r806_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)] := by
    let c8r806targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)]]
    let c8r806choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r806targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)] c8r806choice = true := by decide
    refine ⟨c8r806targets, c8r806choice, ?_, checked⟩
    intro S h
    simp only [c8r806targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 30 _ (by rfl)))
  have c8r807_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)] := by
    let c8r807targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)]]
    let c8r807choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,1),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r807targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)] c8r807choice = true := by decide
    refine ⟨c8r807targets, c8r807choice, ?_, checked⟩
    intro S h
    simp only [c8r807targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 1 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r800_closed
  · subst row; exact c8r801_closed
  · subst row; exact c8r802_closed
  · subst row; exact c8r803_closed
  · subst row; exact c8r804_closed
  · subst row; exact c8r805_closed
  · subst row; exact c8r806_closed
  · subst row; exact c8r807_closed
theorem C8R00800G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r808_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)] := by
    let c8r808targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)]]
    let c8r808choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,2),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r808targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)] c8r808choice = true := by decide
    refine ⟨c8r808targets, c8r808choice, ?_, checked⟩
    intro S h
    simp only [c8r808targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 4 _ (by rfl)))
  have c8r809_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)] := by
    let c8r809targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)]]
    let c8r809choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r809targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)] c8r809choice = true := by decide
    refine ⟨c8r809targets, c8r809choice, ?_, checked⟩
    intro S h
    simp only [c8r809targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 7 _ (by rfl)))
  have c8r810_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)] := by
    let c8r810targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)]]
    let c8r810choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r810targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)] c8r810choice = true := by decide
    refine ⟨c8r810targets, c8r810choice, ?_, checked⟩
    intro S h
    simp only [c8r810targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 10 _ (by rfl)))
  have c8r811_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)] := by
    let c8r811targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)]]
    let c8r811choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0))),((3,3),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r811targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)] c8r811choice = true := by decide
    refine ⟨c8r811targets, c8r811choice, ?_, checked⟩
    intro S h
    simp only [c8r811targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 13 _ (by rfl)))
  have c8r812_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)] := by
    let c8r812targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]]
    let c8r812choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,5),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r812targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)] c8r812choice = true := by decide
    refine ⟨c8r812targets, c8r812choice, ?_, checked⟩
    intro S h
    simp only [c8r812targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 16 _ (by rfl)))
  have c8r813_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)] := by
    let c8r813targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)]]
    let c8r813choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r813targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)] c8r813choice = true := by decide
    refine ⟨c8r813targets, c8r813choice, ?_, checked⟩
    intro S h
    simp only [c8r813targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 19 _ (by rfl)))
  have c8r814_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)] := by
    let c8r814targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)]]
    let c8r814choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,6),(12,(0,0))),((3,4),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r814targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)] c8r814choice = true := by decide
    refine ⟨c8r814targets, c8r814choice, ?_, checked⟩
    intro S h
    simp only [c8r814targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 22 _ (by rfl)))
  have c8r815_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)] := by
    let c8r815targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)]]
    let c8r815choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,3),(13,(0,0))),((3,5),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r815targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)] c8r815choice = true := by decide
    refine ⟨c8r815targets, c8r815choice, ?_, checked⟩
    intro S h
    simp only [c8r815targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 25 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r808_closed
  · subst row; exact c8r809_closed
  · subst row; exact c8r810_closed
  · subst row; exact c8r811_closed
  · subst row; exact c8r812_closed
  · subst row; exact c8r813_closed
  · subst row; exact c8r814_closed
  · subst row; exact c8r815_closed
theorem C8R00800G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r816_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c8r816targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c8r816choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r816targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)] c8r816choice = true := by decide
    refine ⟨c8r816targets, c8r816choice, ?_, checked⟩
    intro S h
    simp only [c8r816targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 30 _ (by rfl)))
  have c8r817_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)] := by
    let c8r817targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)]]
    let c8r817choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r817targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)] c8r817choice = true := by decide
    refine ⟨c8r817targets, c8r817choice, ?_, checked⟩
    intro S h
    simp only [c8r817targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 2 _ (by rfl)))
  have c8r818_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)] := by
    let c8r818targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)]]
    let c8r818choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r818targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)] c8r818choice = true := by decide
    refine ⟨c8r818targets, c8r818choice, ?_, checked⟩
    intro S h
    simp only [c8r818targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 4 _ (by rfl)))
  have c8r819_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)] := by
    let c8r819targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)]]
    let c8r819choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r819targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)] c8r819choice = true := by decide
    refine ⟨c8r819targets, c8r819choice, ?_, checked⟩
    intro S h
    simp only [c8r819targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 6 _ (by rfl)))
  have c8r820_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)] := by
    let c8r820targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)]]
    let c8r820choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r820targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)] c8r820choice = true := by decide
    refine ⟨c8r820targets, c8r820choice, ?_, checked⟩
    intro S h
    simp only [c8r820targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 10 _ (by rfl)))
  have c8r821_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)] := by
    let c8r821targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)]]
    let c8r821choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r821targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)] c8r821choice = true := by decide
    refine ⟨c8r821targets, c8r821choice, ?_, checked⟩
    intro S h
    simp only [c8r821targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 13 _ (by rfl)))
  have c8r822_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)] := by
    let c8r822targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)]]
    let c8r822choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r822targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)] c8r822choice = true := by decide
    refine ⟨c8r822targets, c8r822choice, ?_, checked⟩
    intro S h
    simp only [c8r822targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 16 _ (by rfl)))
  have c8r823_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)] := by
    let c8r823targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4)]]
    let c8r823choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r823targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)] c8r823choice = true := by decide
    refine ⟨c8r823targets, c8r823choice, ?_, checked⟩
    intro S h
    simp only [c8r823targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 20 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r816_closed
  · subst row; exact c8r817_closed
  · subst row; exact c8r818_closed
  · subst row; exact c8r819_closed
  · subst row; exact c8r820_closed
  · subst row; exact c8r821_closed
  · subst row; exact c8r822_closed
  · subst row; exact c8r823_closed
theorem C8R00800G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r824_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)] := by
    let c8r824targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(4,0)]]
    let c8r824choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((3,3),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r824targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)] c8r824choice = true := by decide
    refine ⟨c8r824targets, c8r824choice, ?_, checked⟩
    intro S h
    simp only [c8r824targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 23 _ (by rfl)))
  have c8r825_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)] := by
    let c8r825targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3)]]
    let c8r825choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r825targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)] c8r825choice = true := by decide
    refine ⟨c8r825targets, c8r825choice, ?_, checked⟩
    intro S h
    simp only [c8r825targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 26 _ (by rfl)))
  have c8r826_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)] := by
    let c8r826targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1)]]
    let c8r826choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,2),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r826targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)] c8r826choice = true := by decide
    refine ⟨c8r826targets, c8r826choice, ?_, checked⟩
    intro S h
    simp only [c8r826targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 29 _ (by rfl)))
  have c8r827_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)] := by
    let c8r827targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0)]]
    let c8r827choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,-1),(13,(0,1))),((4,1),(14,(0,0))),((5,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r827targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)] c8r827choice = true := by decide
    refine ⟨c8r827targets, c8r827choice, ?_, checked⟩
    intro S h
    simp only [c8r827targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 31 _ (by rfl)))
  have c8r828_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)] := by
    let c8r828targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c8r828choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r828targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)] c8r828choice = true := by decide
    refine ⟨c8r828targets, c8r828choice, ?_, checked⟩
    intro S h
    simp only [c8r828targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 3 _ (by rfl)))
  have c8r829_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)] := by
    let c8r829targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)]]
    let c8r829choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r829targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)] c8r829choice = true := by decide
    refine ⟨c8r829targets, c8r829choice, ?_, checked⟩
    intro S h
    simp only [c8r829targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 6 _ (by rfl)))
  have c8r830_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)] := by
    let c8r830targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)]]
    let c8r830choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r830targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)] c8r830choice = true := by decide
    refine ⟨c8r830targets, c8r830choice, ?_, checked⟩
    intro S h
    simp only [c8r830targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 8 _ (by rfl)))
  have c8r831_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)] := by
    let c8r831targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)]]
    let c8r831choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r831targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)] c8r831choice = true := by decide
    refine ⟨c8r831targets, c8r831choice, ?_, checked⟩
    intro S h
    simp only [c8r831targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L11_lift _ (familyLookup_sound F9B001L11 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 12 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r824_closed
  · subst row; exact c8r825_closed
  · subst row; exact c8r826_closed
  · subst row; exact c8r827_closed
  · subst row; exact c8r828_closed
  · subst row; exact c8r829_closed
  · subst row; exact c8r830_closed
  · subst row; exact c8r831_closed
theorem C8R00800_closed (row : List GridPoint) (h : FamilyMember row F8B000L25) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L25, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00800G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00800G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00800G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00800G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00800G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00800G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00800G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00800G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00800G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00800G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00800G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00800G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00800G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00800G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00800G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00800G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00800G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00800G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00800G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00800G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00800G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00800G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00800G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00800G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00800G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00800G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00800G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00800G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00800G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00800G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00800G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00800G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
