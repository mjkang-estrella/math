import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00224_closed (row : List GridPoint) (h : FamilyMember row F8B000L7) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r224_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3)] := by
    let c8r224targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3)]]
    let c8r224choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r224targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3)] c8r224choice = true := by decide
    refine ⟨c8r224targets, c8r224choice, ?_, checked⟩
    intro S h
    simp only [c8r224targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 24 _ (by rfl)))
  have c8r225_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0)] := by
    let c8r225targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0),(4,0)]]
    let c8r225choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,-1),(12,(0,1))),((3,1),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r225targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0)] c8r225choice = true := by decide
    refine ⟨c8r225targets, c8r225choice, ?_, checked⟩
    intro S h
    simp only [c8r225targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 26 _ (by rfl)))
  have c8r226_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2)] := by
    let c8r226targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2)]]
    let c8r226choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r226targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2)] c8r226choice = true := by decide
    refine ⟨c8r226targets, c8r226choice, ?_, checked⟩
    intro S h
    simp only [c8r226targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 29 _ (by rfl)))
  have c8r227_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3)] := by
    let c8r227targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3)]]
    let c8r227choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r227targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3)] c8r227choice = true := by decide
    refine ⟨c8r227targets, c8r227choice, ?_, checked⟩
    intro S h
    simp only [c8r227targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 0 _ (by rfl)))
  have c8r228_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2)] := by
    let c8r228targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2)]]
    let c8r228choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r228targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2)] c8r228choice = true := by decide
    refine ⟨c8r228targets, c8r228choice, ?_, checked⟩
    intro S h
    simp only [c8r228targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 3 _ (by rfl)))
  have c8r229_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4)] := by
    let c8r229targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4)]]
    let c8r229choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r229targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4)] c8r229choice = true := by decide
    refine ⟨c8r229targets, c8r229choice, ?_, checked⟩
    intro S h
    simp only [c8r229targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 6 _ (by rfl)))
  have c8r230_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3)] := by
    let c8r230targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3)]]
    let c8r230choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r230targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3)] c8r230choice = true := by decide
    refine ⟨c8r230targets, c8r230choice, ?_, checked⟩
    intro S h
    simp only [c8r230targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 9 _ (by rfl)))
  have c8r231_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)] := by
    let c8r231targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)]]
    let c8r231choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r231targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)] c8r231choice = true := by decide
    refine ⟨c8r231targets, c8r231choice, ?_, checked⟩
    intro S h
    simp only [c8r231targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 14 _ (by rfl)))
  have c8r232_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0)] := by
    let c8r232targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0),(4,0)]]
    let c8r232choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r232targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0)] c8r232choice = true := by decide
    refine ⟨c8r232targets, c8r232choice, ?_, checked⟩
    intro S h
    simp only [c8r232targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 16 _ (by rfl)))
  have c8r233_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,1)] := by
    let c8r233targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,1),(4,1)]]
    let c8r233choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r233targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,1)] c8r233choice = true := by decide
    refine ⟨c8r233targets, c8r233choice, ?_, checked⟩
    intro S h
    simp only [c8r233targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 18 _ (by rfl)))
  have c8r234_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3)] := by
    let c8r234targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,3)]]
    let c8r234choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r234targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3)] c8r234choice = true := by decide
    refine ⟨c8r234targets, c8r234choice, ?_, checked⟩
    intro S h
    simp only [c8r234targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 22 _ (by rfl)))
  have c8r235_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0)] := by
    let c8r235targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(4,0)]]
    let c8r235choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r235targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0)] c8r235choice = true := by decide
    refine ⟨c8r235targets, c8r235choice, ?_, checked⟩
    intro S h
    simp only [c8r235targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 25 _ (by rfl)))
  have c8r236_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2)] := by
    let c8r236targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2),(4,2)]]
    let c8r236choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,3),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r236targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2)] c8r236choice = true := by decide
    refine ⟨c8r236targets, c8r236choice, ?_, checked⟩
    intro S h
    simp only [c8r236targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 28 _ (by rfl)))
  have c8r237_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1)] := by
    let c8r237targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1),(4,1)]]
    let c8r237choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((3,-1),(11,(0,1))),((3,2),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r237targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1)] c8r237choice = true := by decide
    refine ⟨c8r237targets, c8r237choice, ?_, checked⟩
    intro S h
    simp only [c8r237targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 31 _ (by rfl)))
  have c8r238_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0)] := by
    let c8r238targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0),(5,0)]]
    let c8r238choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,-1),(13,(0,1))),((4,1),(14,(0,0))),((5,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r238targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0)] c8r238choice = true := by decide
    refine ⟨c8r238targets, c8r238choice, ?_, checked⟩
    intro S h
    simp only [c8r238targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 1 _ (by rfl)))
  have c8r239_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3)] := by
    let c8r239targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,3)]]
    let c8r239choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r239targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3)] c8r239choice = true := by decide
    refine ⟨c8r239targets, c8r239choice, ?_, checked⟩
    intro S h
    simp only [c8r239targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 5 _ (by rfl)))
  have c8r240_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1)] := by
    let c8r240targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(4,1)]]
    let c8r240choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r240targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1)] c8r240choice = true := by decide
    refine ⟨c8r240targets, c8r240choice, ?_, checked⟩
    intro S h
    simp only [c8r240targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 8 _ (by rfl)))
  have c8r241_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2)] := by
    let c8r241targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(4,2)]]
    let c8r241choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r241targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2)] c8r241choice = true := by decide
    refine ⟨c8r241targets, c8r241choice, ?_, checked⟩
    intro S h
    simp only [c8r241targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 10 _ (by rfl)))
  have c8r242_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4)] := by
    let c8r242targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,4)]]
    let c8r242choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,5),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r242targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4)] c8r242choice = true := by decide
    refine ⟨c8r242targets, c8r242choice, ?_, checked⟩
    intro S h
    simp only [c8r242targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 14 _ (by rfl)))
  have c8r243_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2)] := by
    let c8r243targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(4,2)]]
    let c8r243choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r243targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2)] c8r243choice = true := by decide
    refine ⟨c8r243targets, c8r243choice, ?_, checked⟩
    intro S h
    simp only [c8r243targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 17 _ (by rfl)))
  have c8r244_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3)] := by
    let c8r244targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(4,3)]]
    let c8r244choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r244targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3)] c8r244choice = true := by decide
    refine ⟨c8r244targets, c8r244choice, ?_, checked⟩
    intro S h
    simp only [c8r244targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 19 _ (by rfl)))
  have c8r245_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2)] := by
    let c8r245targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,2)]]
    let c8r245choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r245targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2)] c8r245choice = true := by decide
    refine ⟨c8r245targets, c8r245choice, ?_, checked⟩
    intro S h
    simp only [c8r245targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 23 _ (by rfl)))
  have c8r246_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3)] := by
    let c8r246targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,3)]]
    let c8r246choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r246targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3)] c8r246choice = true := by decide
    refine ⟨c8r246targets, c8r246choice, ?_, checked⟩
    intro S h
    simp only [c8r246targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 26 _ (by rfl)))
  have c8r247_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2)] := by
    let c8r247targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(5,2)]]
    let c8r247choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0))),((4,3),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r247targets [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2)] c8r247choice = true := by decide
    refine ⟨c8r247targets, c8r247choice, ?_, checked⟩
    intro S h
    simp only [c8r247targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 29 _ (by rfl)))
  have c8r248_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r248targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r248choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r248targets [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3)] c8r248choice = true := by decide
    refine ⟨c8r248targets, c8r248choice, ?_, checked⟩
    intro S h
    simp only [c8r248targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 3 _ (by rfl)))
  have c8r249_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r249targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r249choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r249targets [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0)] c8r249choice = true := by decide
    refine ⟨c8r249targets, c8r249choice, ?_, checked⟩
    intro S h
    simp only [c8r249targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 6 _ (by rfl)))
  have c8r250_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r250targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r250choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r250targets [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,1)] c8r250choice = true := by decide
    refine ⟨c8r250targets, c8r250choice, ?_, checked⟩
    intro S h
    simp only [c8r250targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 8 _ (by rfl)))
  have c8r251_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r251targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r251choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r251targets [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,2)] c8r251choice = true := by decide
    refine ⟨c8r251targets, c8r251choice, ?_, checked⟩
    intro S h
    simp only [c8r251targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 10 _ (by rfl)))
  have c8r252_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1)] := by
    let c8r252targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c8r252choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r252targets [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1)] c8r252choice = true := by decide
    refine ⟨c8r252targets, c8r252choice, ?_, checked⟩
    intro S h
    simp only [c8r252targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 13 _ (by rfl)))
  have c8r253_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(4,0)] := by
    let c8r253targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c8r253choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r253targets [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(4,0)] c8r253choice = true := by decide
    refine ⟨c8r253targets, c8r253choice, ?_, checked⟩
    intro S h
    simp only [c8r253targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 15 _ (by rfl)))
  have c8r254_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(3,2)] := by
    let c8r254targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c8r254choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r254targets [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(3,2)] c8r254choice = true := by decide
    refine ⟨c8r254targets, c8r254choice, ?_, checked⟩
    intro S h
    simp only [c8r254targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 18 _ (by rfl)))
  have c8r255_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(4,1)] := by
    let c8r255targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c8r255choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r255targets [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(4,1)] c8r255choice = true := by decide
    refine ⟨c8r255targets, c8r255choice, ?_, checked⟩
    intro S h
    simp only [c8r255targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L36_lift _ (familyLookup_sound F9B003L36 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L24_lift _ (familyLookup_sound F9B000L24 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 21 _ (by rfl)))
  simp only [F8B000L7, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c8r224_closed
  · subst row; exact c8r225_closed
  · subst row; exact c8r226_closed
  · subst row; exact c8r227_closed
  · subst row; exact c8r228_closed
  · subst row; exact c8r229_closed
  · subst row; exact c8r230_closed
  · subst row; exact c8r231_closed
  · subst row; exact c8r232_closed
  · subst row; exact c8r233_closed
  · subst row; exact c8r234_closed
  · subst row; exact c8r235_closed
  · subst row; exact c8r236_closed
  · subst row; exact c8r237_closed
  · subst row; exact c8r238_closed
  · subst row; exact c8r239_closed
  · subst row; exact c8r240_closed
  · subst row; exact c8r241_closed
  · subst row; exact c8r242_closed
  · subst row; exact c8r243_closed
  · subst row; exact c8r244_closed
  · subst row; exact c8r245_closed
  · subst row; exact c8r246_closed
  · subst row; exact c8r247_closed
  · subst row; exact c8r248_closed
  · subst row; exact c8r249_closed
  · subst row; exact c8r250_closed
  · subst row; exact c8r251_closed
  · subst row; exact c8r252_closed
  · subst row; exact c8r253_closed
  · subst row; exact c8r254_closed
  · subst row; exact c8r255_closed
end Polyomino57
