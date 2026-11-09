import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01280G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1280_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)] := by
    let c8r1280targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)]]
    let c8r1280choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1280targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)] c8r1280choice = true := by decide
    refine ⟨c8r1280targets, c8r1280choice, ?_, checked⟩
    intro S h
    simp only [c8r1280targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 17 _ (by rfl)))
  have c8r1281_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)] := by
    let c8r1281targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)]]
    let c8r1281choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1281targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)] c8r1281choice = true := by decide
    refine ⟨c8r1281targets, c8r1281choice, ?_, checked⟩
    intro S h
    simp only [c8r1281targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 21 _ (by rfl)))
  have c8r1282_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)] := by
    let c8r1282targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)]]
    let c8r1282choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1282targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)] c8r1282choice = true := by decide
    refine ⟨c8r1282targets, c8r1282choice, ?_, checked⟩
    intro S h
    simp only [c8r1282targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 24 _ (by rfl)))
  have c8r1283_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)] := by
    let c8r1283targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)]]
    let c8r1283choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1283targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)] c8r1283choice = true := by decide
    refine ⟨c8r1283targets, c8r1283choice, ?_, checked⟩
    intro S h
    simp only [c8r1283targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 26 _ (by rfl)))
  have c8r1284_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)] := by
    let c8r1284targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)]]
    let c8r1284choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1284targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)] c8r1284choice = true := by decide
    refine ⟨c8r1284targets, c8r1284choice, ?_, checked⟩
    intro S h
    simp only [c8r1284targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 30 _ (by rfl)))
  have c8r1285_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)] := by
    let c8r1285targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)]]
    let c8r1285choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1285targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)] c8r1285choice = true := by decide
    refine ⟨c8r1285targets, c8r1285choice, ?_, checked⟩
    intro S h
    simp only [c8r1285targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 1 _ (by rfl)))
  have c8r1286_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)] := by
    let c8r1286targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)]]
    let c8r1286choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1286targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)] c8r1286choice = true := by decide
    refine ⟨c8r1286targets, c8r1286choice, ?_, checked⟩
    intro S h
    simp only [c8r1286targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 4 _ (by rfl)))
  have c8r1287_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)] := by
    let c8r1287targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1287choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1287targets [(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)] c8r1287choice = true := by decide
    refine ⟨c8r1287targets, c8r1287choice, ?_, checked⟩
    intro S h
    simp only [c8r1287targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L16_lift _ (familyLookup_sound F9B003L16 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 10 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1280_closed
  · subst row; exact c8r1281_closed
  · subst row; exact c8r1282_closed
  · subst row; exact c8r1283_closed
  · subst row; exact c8r1284_closed
  · subst row; exact c8r1285_closed
  · subst row; exact c8r1286_closed
  · subst row; exact c8r1287_closed
theorem C8R01280G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1288_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1288targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1288choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1288targets [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)] c8r1288choice = true := by decide
    refine ⟨c8r1288targets, c8r1288choice, ?_, checked⟩
    intro S h
    simp only [c8r1288targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L16_lift _ (familyLookup_sound F9B003L16 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 16 _ (by rfl)))
  have c8r1289_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r1289targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r1289choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1289targets [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)] c8r1289choice = true := by decide
    refine ⟨c8r1289targets, c8r1289choice, ?_, checked⟩
    intro S h
    simp only [c8r1289targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L16_lift _ (familyLookup_sound F9B003L16 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 19 _ (by rfl)))
  have c8r1290_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r1290targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r1290choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1290targets [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)] c8r1290choice = true := by decide
    refine ⟨c8r1290targets, c8r1290choice, ?_, checked⟩
    intro S h
    simp only [c8r1290targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L16_lift _ (familyLookup_sound F9B003L16 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 21 _ (by rfl)))
  have c8r1291_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r1291targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r1291choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1291targets [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)] c8r1291choice = true := by decide
    refine ⟨c8r1291targets, c8r1291choice, ?_, checked⟩
    intro S h
    simp only [c8r1291targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L16_lift _ (familyLookup_sound F9B003L16 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 23 _ (by rfl)))
  have c8r1292_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)] := by
    let c8r1292targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1292choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1292targets [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)] c8r1292choice = true := by decide
    refine ⟨c8r1292targets, c8r1292choice, ?_, checked⟩
    intro S h
    simp only [c8r1292targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L16_lift _ (familyLookup_sound F9B003L16 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 26 _ (by rfl)))
  have c8r1293_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)] := by
    let c8r1293targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c8r1293choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1293targets [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)] c8r1293choice = true := by decide
    refine ⟨c8r1293targets, c8r1293choice, ?_, checked⟩
    intro S h
    simp only [c8r1293targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L16_lift _ (familyLookup_sound F9B003L16 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 28 _ (by rfl)))
  have c8r1294_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)] := by
    let c8r1294targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c8r1294choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1294targets [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)] c8r1294choice = true := by decide
    refine ⟨c8r1294targets, c8r1294choice, ?_, checked⟩
    intro S h
    simp only [c8r1294targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L16_lift _ (familyLookup_sound F9B003L16 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 31 _ (by rfl)))
  have c8r1295_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)] := by
    let c8r1295targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c8r1295choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1295targets [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)] c8r1295choice = true := by decide
    refine ⟨c8r1295targets, c8r1295choice, ?_, checked⟩
    intro S h
    simp only [c8r1295targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 2 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1288_closed
  · subst row; exact c8r1289_closed
  · subst row; exact c8r1290_closed
  · subst row; exact c8r1291_closed
  · subst row; exact c8r1292_closed
  · subst row; exact c8r1293_closed
  · subst row; exact c8r1294_closed
  · subst row; exact c8r1295_closed
theorem C8R01280G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1296_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)] := by
    let c8r1296targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1296choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1296targets [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)] c8r1296choice = true := by decide
    refine ⟨c8r1296targets, c8r1296choice, ?_, checked⟩
    intro S h
    simp only [c8r1296targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 7 _ (by rfl)))
  have c8r1297_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)] := by
    let c8r1297targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)]]
    let c8r1297choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1297targets [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)] c8r1297choice = true := by decide
    refine ⟨c8r1297targets, c8r1297choice, ?_, checked⟩
    intro S h
    simp only [c8r1297targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 9 _ (by rfl)))
  have c8r1298_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)] := by
    let c8r1298targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1)]]
    let c8r1298choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1298targets [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)] c8r1298choice = true := by decide
    refine ⟨c8r1298targets, c8r1298choice, ?_, checked⟩
    intro S h
    simp only [c8r1298targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 11 _ (by rfl)))
  have c8r1299_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)] := by
    let c8r1299targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1)]]
    let c8r1299choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1299targets [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)] c8r1299choice = true := by decide
    refine ⟨c8r1299targets, c8r1299choice, ?_, checked⟩
    intro S h
    simp only [c8r1299targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 14 _ (by rfl)))
  have c8r1300_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)] := by
    let c8r1300targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0)]]
    let c8r1300choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1300targets [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)] c8r1300choice = true := by decide
    refine ⟨c8r1300targets, c8r1300choice, ?_, checked⟩
    intro S h
    simp only [c8r1300targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 16 _ (by rfl)))
  have c8r1301_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r1301targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r1301choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1301targets [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)] c8r1301choice = true := by decide
    refine ⟨c8r1301targets, c8r1301choice, ?_, checked⟩
    intro S h
    simp only [c8r1301targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 21 _ (by rfl)))
  have c8r1302_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r1302targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r1302choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1302targets [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)] c8r1302choice = true := by decide
    refine ⟨c8r1302targets, c8r1302choice, ?_, checked⟩
    intro S h
    simp only [c8r1302targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 25 _ (by rfl)))
  have c8r1303_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r1303targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r1303choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1303targets [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)] c8r1303choice = true := by decide
    refine ⟨c8r1303targets, c8r1303choice, ?_, checked⟩
    intro S h
    simp only [c8r1303targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 27 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1296_closed
  · subst row; exact c8r1297_closed
  · subst row; exact c8r1298_closed
  · subst row; exact c8r1299_closed
  · subst row; exact c8r1300_closed
  · subst row; exact c8r1301_closed
  · subst row; exact c8r1302_closed
  · subst row; exact c8r1303_closed
theorem C8R01280G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1304_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r1304targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r1304choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1304targets [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)] c8r1304choice = true := by decide
    refine ⟨c8r1304targets, c8r1304choice, ?_, checked⟩
    intro S h
    simp only [c8r1304targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 29 _ (by rfl)))
  have c8r1305_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r1305targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r1305choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1305targets [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)] c8r1305choice = true := by decide
    refine ⟨c8r1305targets, c8r1305choice, ?_, checked⟩
    intro S h
    simp only [c8r1305targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L20_lift _ (familyLookup_sound F9B003L20 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 0 _ (by rfl)))
  have c8r1306_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)] := by
    let c8r1306targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c8r1306choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1306targets [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)] c8r1306choice = true := by decide
    refine ⟨c8r1306targets, c8r1306choice, ?_, checked⟩
    intro S h
    simp only [c8r1306targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 3 _ (by rfl)))
  have c8r1307_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)] := by
    let c8r1307targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c8r1307choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1307targets [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)] c8r1307choice = true := by decide
    refine ⟨c8r1307targets, c8r1307choice, ?_, checked⟩
    intro S h
    simp only [c8r1307targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 6 _ (by rfl)))
  have c8r1308_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)] := by
    let c8r1308targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c8r1308choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1308targets [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)] c8r1308choice = true := by decide
    refine ⟨c8r1308targets, c8r1308choice, ?_, checked⟩
    intro S h
    simp only [c8r1308targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 9 _ (by rfl)))
  have c8r1309_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)] := by
    let c8r1309targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c8r1309choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1309targets [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)] c8r1309choice = true := by decide
    refine ⟨c8r1309targets, c8r1309choice, ?_, checked⟩
    intro S h
    simp only [c8r1309targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 12 _ (by rfl)))
  have c8r1310_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)] := by
    let c8r1310targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1310choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1310targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)] c8r1310choice = true := by decide
    refine ⟨c8r1310targets, c8r1310choice, ?_, checked⟩
    intro S h
    simp only [c8r1310targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 17 _ (by rfl)))
  have c8r1311_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)] := by
    let c8r1311targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c8r1311choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1311targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)] c8r1311choice = true := by decide
    refine ⟨c8r1311targets, c8r1311choice, ?_, checked⟩
    intro S h
    simp only [c8r1311targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L47_lift _ (familyLookup_sound F9B003L47 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L17_lift _ (familyLookup_sound F9B003L17 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L8_lift _ (familyLookup_sound F9B002L8 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L21_lift _ (familyLookup_sound F9B003L21 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 19 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1304_closed
  · subst row; exact c8r1305_closed
  · subst row; exact c8r1306_closed
  · subst row; exact c8r1307_closed
  · subst row; exact c8r1308_closed
  · subst row; exact c8r1309_closed
  · subst row; exact c8r1310_closed
  · subst row; exact c8r1311_closed
theorem C8R01280_closed (row : List GridPoint) (h : FamilyMember row F8B000L40) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L40, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01280G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01280G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01280G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01280G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01280G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01280G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01280G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01280G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01280G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01280G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01280G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01280G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01280G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01280G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01280G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01280G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01280G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01280G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01280G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01280G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01280G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01280G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01280G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01280G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01280G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01280G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01280G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01280G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01280G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01280G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01280G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01280G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
