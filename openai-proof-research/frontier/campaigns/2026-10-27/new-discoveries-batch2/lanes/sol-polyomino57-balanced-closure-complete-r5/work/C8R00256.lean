import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00256_closed (row : List GridPoint) (h : FamilyMember row F8B000L8) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r256_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2)] := by
    let c8r256targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2)]]
    let c8r256choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((3,-1),(11,(0,1))),((3,3),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r256targets [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2)] c8r256choice = true := by decide
    refine ⟨c8r256targets, c8r256choice, ?_, checked⟩
    intro S h
    simp only [c8r256targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 26 _ (by rfl)))
  have c8r257_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0)] := by
    let c8r257targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)]]
    let c8r257choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r257targets [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0)] c8r257choice = true := by decide
    refine ⟨c8r257targets, c8r257choice, ?_, checked⟩
    intro S h
    simp only [c8r257targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 28 _ (by rfl)))
  have c8r258_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1)] := by
    let c8r258targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1)]]
    let c8r258choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r258targets [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1)] c8r258choice = true := by decide
    refine ⟨c8r258targets, c8r258choice, ?_, checked⟩
    intro S h
    simp only [c8r258targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 30 _ (by rfl)))
  have c8r259_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(4,1)] := by
    let c8r259targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1)]]
    let c8r259choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,-1),(12,(0,1))),((4,2),(13,(0,0))),((5,0),(14,(0,0))),((5,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r259targets [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(4,1)] c8r259choice = true := by decide
    refine ⟨c8r259targets, c8r259choice, ?_, checked⟩
    intro S h
    simp only [c8r259targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 1 _ (by rfl)))
  have c8r260_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(5,0)] := by
    let c8r260targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0)]]
    let c8r260choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,-1),(14,(0,1))),((5,1),(15,(0,0))),((6,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r260targets [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(5,0)] c8r260choice = true := by decide
    refine ⟨c8r260targets, c8r260choice, ?_, checked⟩
    intro S h
    simp only [c8r260targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 3 _ (by rfl)))
  have c8r261_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r261targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r261choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,6),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r261targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r261choice = true := by decide
    refine ⟨c8r261targets, c8r261choice, ?_, checked⟩
    intro S h
    simp only [c8r261targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 9 _ (by rfl)))
  have c8r262_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c8r262targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c8r262choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r262targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1)] c8r262choice = true := by decide
    refine ⟨c8r262targets, c8r262choice, ?_, checked⟩
    intro S h
    simp only [c8r262targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 14 _ (by rfl)))
  have c8r263_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c8r263targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c8r263choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r263targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2)] c8r263choice = true := by decide
    refine ⟨c8r263targets, c8r263choice, ?_, checked⟩
    intro S h
    simp only [c8r263targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 17 _ (by rfl)))
  have c8r264_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c8r264targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c8r264choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r264targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3)] c8r264choice = true := by decide
    refine ⟨c8r264targets, c8r264choice, ?_, checked⟩
    intro S h
    simp only [c8r264targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 19 _ (by rfl)))
  have c8r265_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r265targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r265choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r265targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4)] c8r265choice = true := by decide
    refine ⟨c8r265targets, c8r265choice, ?_, checked⟩
    intro S h
    simp only [c8r265targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 21 _ (by rfl)))
  have c8r266_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c8r266targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c8r266choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r266targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1)] c8r266choice = true := by decide
    refine ⟨c8r266targets, c8r266choice, ?_, checked⟩
    intro S h
    simp only [c8r266targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 25 _ (by rfl)))
  have c8r267_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2)] := by
    let c8r267targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
    let c8r267choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r267targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2)] c8r267choice = true := by decide
    refine ⟨c8r267targets, c8r267choice, ?_, checked⟩
    intro S h
    simp only [c8r267targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 28 _ (by rfl)))
  have c8r268_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3)] := by
    let c8r268targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
    let c8r268choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r268targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3)] c8r268choice = true := by decide
    refine ⟨c8r268targets, c8r268choice, ?_, checked⟩
    intro S h
    simp only [c8r268targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 31 _ (by rfl)))
  have c8r269_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1)] := by
    let c8r269targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
    let c8r269choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r269targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1)] c8r269choice = true := by decide
    refine ⟨c8r269targets, c8r269choice, ?_, checked⟩
    intro S h
    simp only [c8r269targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 2 _ (by rfl)))
  have c8r270_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3)] := by
    let c8r270targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
    let c8r270choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r270targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3)] c8r270choice = true := by decide
    refine ⟨c8r270targets, c8r270choice, ?_, checked⟩
    intro S h
    simp only [c8r270targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 5 _ (by rfl)))
  have c8r271_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2)] := by
    let c8r271targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
    let c8r271choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r271targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2)] c8r271choice = true := by decide
    refine ⟨c8r271targets, c8r271choice, ?_, checked⟩
    intro S h
    simp only [c8r271targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 8 _ (by rfl)))
  have c8r272_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4)] := by
    let c8r272targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
    let c8r272choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r272targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4)] c8r272choice = true := by decide
    refine ⟨c8r272targets, c8r272choice, ?_, checked⟩
    intro S h
    simp only [c8r272targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 11 _ (by rfl)))
  have c8r273_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3)] := by
    let c8r273targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
    let c8r273choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r273targets [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3)] c8r273choice = true := by decide
    refine ⟨c8r273targets, c8r273choice, ?_, checked⟩
    intro S h
    simp only [c8r273targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 14 _ (by rfl)))
  have c8r274_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2)] := by
    let c8r274targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]
    let c8r274choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r274targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2)] c8r274choice = true := by decide
    refine ⟨c8r274targets, c8r274choice, ?_, checked⟩
    intro S h
    simp only [c8r274targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 19 _ (by rfl)))
  have c8r275_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0)] := by
    let c8r275targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]
    let c8r275choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r275targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0)] c8r275choice = true := by decide
    refine ⟨c8r275targets, c8r275choice, ?_, checked⟩
    intro S h
    simp only [c8r275targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 21 _ (by rfl)))
  have c8r276_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1)] := by
    let c8r276targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
    let c8r276choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r276targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1)] c8r276choice = true := by decide
    refine ⟨c8r276targets, c8r276choice, ?_, checked⟩
    intro S h
    simp only [c8r276targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 23 _ (by rfl)))
  have c8r277_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3)] := by
    let c8r277targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)]]
    let c8r277choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r277targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3)] c8r277choice = true := by decide
    refine ⟨c8r277targets, c8r277choice, ?_, checked⟩
    intro S h
    simp only [c8r277targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 27 _ (by rfl)))
  have c8r278_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1)] := by
    let c8r278targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)]]
    let c8r278choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r278targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1)] c8r278choice = true := by decide
    refine ⟨c8r278targets, c8r278choice, ?_, checked⟩
    intro S h
    simp only [c8r278targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 30 _ (by rfl)))
  have c8r279_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2)] := by
    let c8r279targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)]]
    let c8r279choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r279targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2)] c8r279choice = true := by decide
    refine ⟨c8r279targets, c8r279choice, ?_, checked⟩
    intro S h
    simp only [c8r279targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 0 _ (by rfl)))
  have c8r280_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1)] := by
    let c8r280targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
    let c8r280choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r280targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1)] c8r280choice = true := by decide
    refine ⟨c8r280targets, c8r280choice, ?_, checked⟩
    intro S h
    simp only [c8r280targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 3 _ (by rfl)))
  have c8r281_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2)] := by
    let c8r281targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)]]
    let c8r281choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r281targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2)] c8r281choice = true := by decide
    refine ⟨c8r281targets, c8r281choice, ?_, checked⟩
    intro S h
    simp only [c8r281targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 6 _ (by rfl)))
  have c8r282_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1)] := by
    let c8r282targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)]]
    let c8r282choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r282targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1)] c8r282choice = true := by decide
    refine ⟨c8r282targets, c8r282choice, ?_, checked⟩
    intro S h
    simp only [c8r282targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 9 _ (by rfl)))
  have c8r283_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4)] := by
    let c8r283targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)]]
    let c8r283choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r283targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4)] c8r283choice = true := by decide
    refine ⟨c8r283targets, c8r283choice, ?_, checked⟩
    intro S h
    simp only [c8r283targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 13 _ (by rfl)))
  have c8r284_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2)] := by
    let c8r284targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)]]
    let c8r284choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r284targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2)] c8r284choice = true := by decide
    refine ⟨c8r284targets, c8r284choice, ?_, checked⟩
    intro S h
    simp only [c8r284targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 16 _ (by rfl)))
  have c8r285_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3)] := by
    let c8r285targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)]]
    let c8r285choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r285targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3)] c8r285choice = true := by decide
    refine ⟨c8r285targets, c8r285choice, ?_, checked⟩
    intro S h
    simp only [c8r285targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 18 _ (by rfl)))
  have c8r286_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2)] := by
    let c8r286targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)]]
    let c8r286choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r286targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2)] c8r286choice = true := by decide
    refine ⟨c8r286targets, c8r286choice, ?_, checked⟩
    intro S h
    simp only [c8r286targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 22 _ (by rfl)))
  have c8r287_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3)] := by
    let c8r287targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)]]
    let c8r287choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r287targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3)] c8r287choice = true := by decide
    refine ⟨c8r287targets, c8r287choice, ?_, checked⟩
    intro S h
    simp only [c8r287targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 25 _ (by rfl)))
  simp only [F8B000L8, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c8r256_closed
  · subst row; exact c8r257_closed
  · subst row; exact c8r258_closed
  · subst row; exact c8r259_closed
  · subst row; exact c8r260_closed
  · subst row; exact c8r261_closed
  · subst row; exact c8r262_closed
  · subst row; exact c8r263_closed
  · subst row; exact c8r264_closed
  · subst row; exact c8r265_closed
  · subst row; exact c8r266_closed
  · subst row; exact c8r267_closed
  · subst row; exact c8r268_closed
  · subst row; exact c8r269_closed
  · subst row; exact c8r270_closed
  · subst row; exact c8r271_closed
  · subst row; exact c8r272_closed
  · subst row; exact c8r273_closed
  · subst row; exact c8r274_closed
  · subst row; exact c8r275_closed
  · subst row; exact c8r276_closed
  · subst row; exact c8r277_closed
  · subst row; exact c8r278_closed
  · subst row; exact c8r279_closed
  · subst row; exact c8r280_closed
  · subst row; exact c8r281_closed
  · subst row; exact c8r282_closed
  · subst row; exact c8r283_closed
  · subst row; exact c8r284_closed
  · subst row; exact c8r285_closed
  · subst row; exact c8r286_closed
  · subst row; exact c8r287_closed
end Polyomino57
