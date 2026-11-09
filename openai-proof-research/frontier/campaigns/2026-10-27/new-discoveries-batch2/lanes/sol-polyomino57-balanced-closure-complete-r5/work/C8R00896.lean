import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00896G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r896_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)] := by
    let c8r896targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c8r896choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r896targets [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)] c8r896choice = true := by decide
    refine ⟨c8r896targets, c8r896choice, ?_, checked⟩
    intro S h
    simp only [c8r896targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 24 _ (by rfl)))
  have c8r897_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)] := by
    let c8r897targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c8r897choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r897targets [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)] c8r897choice = true := by decide
    refine ⟨c8r897targets, c8r897choice, ?_, checked⟩
    intro S h
    simp only [c8r897targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 27 _ (by rfl)))
  have c8r898_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)] := by
    let c8r898targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c8r898choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,5),(10,(0,0))),((4,3),(11,(0,0))),((4,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r898targets [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)] c8r898choice = true := by decide
    refine ⟨c8r898targets, c8r898choice, ?_, checked⟩
    intro S h
    simp only [c8r898targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 30 _ (by rfl)))
  have c8r899_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)] := by
    let c8r899targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c8r899choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r899targets [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)] c8r899choice = true := by decide
    refine ⟨c8r899targets, c8r899choice, ?_, checked⟩
    intro S h
    simp only [c8r899targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 1 _ (by rfl)))
  have c8r900_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r900targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r900choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r900targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)] c8r900choice = true := by decide
    refine ⟨c8r900targets, c8r900choice, ?_, checked⟩
    intro S h
    simp only [c8r900targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 6 _ (by rfl)))
  have c8r901_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)] := by
    let c8r901targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c8r901choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r901targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)] c8r901choice = true := by decide
    refine ⟨c8r901targets, c8r901choice, ?_, checked⟩
    intro S h
    simp only [c8r901targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 10 _ (by rfl)))
  have c8r902_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)] := by
    let c8r902targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c8r902choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r902targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)] c8r902choice = true := by decide
    refine ⟨c8r902targets, c8r902choice, ?_, checked⟩
    intro S h
    simp only [c8r902targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 13 _ (by rfl)))
  have c8r903_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)] := by
    let c8r903targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c8r903choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r903targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)] c8r903choice = true := by decide
    refine ⟨c8r903targets, c8r903choice, ?_, checked⟩
    intro S h
    simp only [c8r903targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 15 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r896_closed
  · subst row; exact c8r897_closed
  · subst row; exact c8r898_closed
  · subst row; exact c8r899_closed
  · subst row; exact c8r900_closed
  · subst row; exact c8r901_closed
  · subst row; exact c8r902_closed
  · subst row; exact c8r903_closed
theorem C8R00896G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r904_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)] := by
    let c8r904targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c8r904choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,5),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r904targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)] c8r904choice = true := by decide
    refine ⟨c8r904targets, c8r904choice, ?_, checked⟩
    intro S h
    simp only [c8r904targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 19 _ (by rfl)))
  have c8r905_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)] := by
    let c8r905targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c8r905choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r905targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)] c8r905choice = true := by decide
    refine ⟨c8r905targets, c8r905choice, ?_, checked⟩
    intro S h
    simp only [c8r905targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 22 _ (by rfl)))
  have c8r906_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)] := by
    let c8r906targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c8r906choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r906targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)] c8r906choice = true := by decide
    refine ⟨c8r906targets, c8r906choice, ?_, checked⟩
    intro S h
    simp only [c8r906targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 24 _ (by rfl)))
  have c8r907_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)] := by
    let c8r907targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c8r907choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r907targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)] c8r907choice = true := by decide
    refine ⟨c8r907targets, c8r907choice, ?_, checked⟩
    intro S h
    simp only [c8r907targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 28 _ (by rfl)))
  have c8r908_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)] := by
    let c8r908targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c8r908choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,4),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r908targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)] c8r908choice = true := by decide
    refine ⟨c8r908targets, c8r908choice, ?_, checked⟩
    intro S h
    simp only [c8r908targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 31 _ (by rfl)))
  have c8r909_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)] := by
    let c8r909targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c8r909choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,3),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r909targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)] c8r909choice = true := by decide
    refine ⟨c8r909targets, c8r909choice, ?_, checked⟩
    intro S h
    simp only [c8r909targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 2 _ (by rfl)))
  have c8r910_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)] := by
    let c8r910targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)]]
    let c8r910choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r910targets [(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)] c8r910choice = true := by decide
    refine ⟨c8r910targets, c8r910choice, ?_, checked⟩
    intro S h
    simp only [c8r910targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 8 _ (by rfl)))
  have c8r911_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r911targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r911choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r911targets [(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)] c8r911choice = true := by decide
    refine ⟨c8r911targets, c8r911choice, ?_, checked⟩
    intro S h
    simp only [c8r911targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 13 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r904_closed
  · subst row; exact c8r905_closed
  · subst row; exact c8r906_closed
  · subst row; exact c8r907_closed
  · subst row; exact c8r908_closed
  · subst row; exact c8r909_closed
  · subst row; exact c8r910_closed
  · subst row; exact c8r911_closed
theorem C8R00896G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r912_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r912targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r912choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r912targets [(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)] c8r912choice = true := by decide
    refine ⟨c8r912targets, c8r912choice, ?_, checked⟩
    intro S h
    simp only [c8r912targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 18 _ (by rfl)))
  have c8r913_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r913targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r913choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r913targets [(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)] c8r913choice = true := by decide
    refine ⟨c8r913targets, c8r913choice, ?_, checked⟩
    intro S h
    simp only [c8r913targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 22 _ (by rfl)))
  have c8r914_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r914targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r914choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r914targets [(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)] c8r914choice = true := by decide
    refine ⟨c8r914targets, c8r914choice, ?_, checked⟩
    intro S h
    simp only [c8r914targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 24 _ (by rfl)))
  have c8r915_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r915targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r915choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r915targets [(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)] c8r915choice = true := by decide
    refine ⟨c8r915targets, c8r915choice, ?_, checked⟩
    intro S h
    simp only [c8r915targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 26 _ (by rfl)))
  have c8r916_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r916targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r916choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r916targets [(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)] c8r916choice = true := by decide
    refine ⟨c8r916targets, c8r916choice, ?_, checked⟩
    intro S h
    simp only [c8r916targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 2 _ (by rfl)))
  have c8r917_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r917targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r917choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,5),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r917targets [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)] c8r917choice = true := by decide
    refine ⟨c8r917targets, c8r917choice, ?_, checked⟩
    intro S h
    simp only [c8r917targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 9 _ (by rfl)))
  have c8r918_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c8r918targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c8r918choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r918targets [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)] c8r918choice = true := by decide
    refine ⟨c8r918targets, c8r918choice, ?_, checked⟩
    intro S h
    simp only [c8r918targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 13 _ (by rfl)))
  have c8r919_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r919targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r919choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r919targets [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)] c8r919choice = true := by decide
    refine ⟨c8r919targets, c8r919choice, ?_, checked⟩
    intro S h
    simp only [c8r919targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 16 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r912_closed
  · subst row; exact c8r913_closed
  · subst row; exact c8r914_closed
  · subst row; exact c8r915_closed
  · subst row; exact c8r916_closed
  · subst row; exact c8r917_closed
  · subst row; exact c8r918_closed
  · subst row; exact c8r919_closed
theorem C8R00896G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r920_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r920targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r920choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r920targets [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)] c8r920choice = true := by decide
    refine ⟨c8r920targets, c8r920choice, ?_, checked⟩
    intro S h
    simp only [c8r920targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 18 _ (by rfl)))
  have c8r921_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r921targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r921choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r921targets [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)] c8r921choice = true := by decide
    refine ⟨c8r921targets, c8r921choice, ?_, checked⟩
    intro S h
    simp only [c8r921targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 20 _ (by rfl)))
  have c8r922_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r922targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r922choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r922targets [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)] c8r922choice = true := by decide
    refine ⟨c8r922targets, c8r922choice, ?_, checked⟩
    intro S h
    simp only [c8r922targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 23 _ (by rfl)))
  have c8r923_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c8r923targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c8r923choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r923targets [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)] c8r923choice = true := by decide
    refine ⟨c8r923targets, c8r923choice, ?_, checked⟩
    intro S h
    simp only [c8r923targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 26 _ (by rfl)))
  have c8r924_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c8r924targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c8r924choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r924targets [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)] c8r924choice = true := by decide
    refine ⟨c8r924targets, c8r924choice, ?_, checked⟩
    intro S h
    simp only [c8r924targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 28 _ (by rfl)))
  have c8r925_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c8r925targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c8r925choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r925targets [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)] c8r925choice = true := by decide
    refine ⟨c8r925targets, c8r925choice, ?_, checked⟩
    intro S h
    simp only [c8r925targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 31 _ (by rfl)))
  have c8r926_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c8r926targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c8r926choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r926targets [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)] c8r926choice = true := by decide
    refine ⟨c8r926targets, c8r926choice, ?_, checked⟩
    intro S h
    simp only [c8r926targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 2 _ (by rfl)))
  have c8r927_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c8r927targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c8r927choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r927targets [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)] c8r927choice = true := by decide
    refine ⟨c8r927targets, c8r927choice, ?_, checked⟩
    intro S h
    simp only [c8r927targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 5 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r920_closed
  · subst row; exact c8r921_closed
  · subst row; exact c8r922_closed
  · subst row; exact c8r923_closed
  · subst row; exact c8r924_closed
  · subst row; exact c8r925_closed
  · subst row; exact c8r926_closed
  · subst row; exact c8r927_closed
theorem C8R00896_closed (row : List GridPoint) (h : FamilyMember row F8B000L28) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L28, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00896G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00896G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00896G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00896G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00896G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00896G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00896G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00896G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00896G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00896G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00896G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00896G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00896G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00896G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00896G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00896G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00896G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00896G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00896G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00896G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00896G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00896G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00896G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00896G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00896G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00896G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00896G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00896G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00896G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00896G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00896G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00896G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
