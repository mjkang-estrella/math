import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00512G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r512_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r512targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r512choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r512targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)] c8r512choice = true := by decide
    refine ⟨c8r512targets, c8r512choice, ?_, checked⟩
    intro S h
    simp only [c8r512targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 16 _ (by rfl)))
  have c8r513_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2)] := by
    let c8r513targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c8r513choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r513targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2)] c8r513choice = true := by decide
    refine ⟨c8r513targets, c8r513choice, ?_, checked⟩
    intro S h
    simp only [c8r513targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 18 _ (by rfl)))
  have c8r514_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)] := by
    let c8r514targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c8r514choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r514targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)] c8r514choice = true := by decide
    refine ⟨c8r514targets, c8r514choice, ?_, checked⟩
    intro S h
    simp only [c8r514targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 21 _ (by rfl)))
  have c8r515_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)] := by
    let c8r515targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c8r515choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r515targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)] c8r515choice = true := by decide
    refine ⟨c8r515targets, c8r515choice, ?_, checked⟩
    intro S h
    simp only [c8r515targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 23 _ (by rfl)))
  have c8r516_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2)] := by
    let c8r516targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c8r516choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r516targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2)] c8r516choice = true := by decide
    refine ⟨c8r516targets, c8r516choice, ?_, checked⟩
    intro S h
    simp only [c8r516targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 26 _ (by rfl)))
  have c8r517_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1)] := by
    let c8r517targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c8r517choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r517targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1)] c8r517choice = true := by decide
    refine ⟨c8r517targets, c8r517choice, ?_, checked⟩
    intro S h
    simp only [c8r517targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L9_lift _ (familyLookup_sound F9B002L9 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 29 _ (by rfl)))
  have c8r518_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2)] := by
    let c8r518targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)]]
    let c8r518choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,3),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r518targets [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2)] c8r518choice = true := by decide
    refine ⟨c8r518targets, c8r518choice, ?_, checked⟩
    intro S h
    simp only [c8r518targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L26_lift _ (familyLookup_sound F9B000L26 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 2 _ (by rfl)))
  have c8r519_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)] := by
    let c8r519targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)]]
    let c8r519choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r519targets [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)] c8r519choice = true := by decide
    refine ⟨c8r519targets, c8r519choice, ?_, checked⟩
    intro S h
    simp only [c8r519targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 4 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r512_closed
  · subst row; exact c8r513_closed
  · subst row; exact c8r514_closed
  · subst row; exact c8r515_closed
  · subst row; exact c8r516_closed
  · subst row; exact c8r517_closed
  · subst row; exact c8r518_closed
  · subst row; exact c8r519_closed
theorem C8R00512G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r520_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1)] := by
    let c8r520targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)]]
    let c8r520choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r520targets [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1)] c8r520choice = true := by decide
    refine ⟨c8r520targets, c8r520choice, ?_, checked⟩
    intro S h
    simp only [c8r520targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 6 _ (by rfl)))
  have c8r521_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1)] := by
    let c8r521targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)]]
    let c8r521choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r521targets [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1)] c8r521choice = true := by decide
    refine ⟨c8r521targets, c8r521choice, ?_, checked⟩
    intro S h
    simp only [c8r521targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 9 _ (by rfl)))
  have c8r522_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0)] := by
    let c8r522targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)]]
    let c8r522choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,-1),(14,(0,1))),((6,1),(15,(0,0))),((7,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r522targets [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0)] c8r522choice = true := by decide
    refine ⟨c8r522targets, c8r522choice, ?_, checked⟩
    intro S h
    simp only [c8r522targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L15_lift _ (familyLookup_sound F9B002L15 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L16_lift _ (familyLookup_sound F9B002L16 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 11 _ (by rfl)))
  have c8r523_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] := by
    let c8r523targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)]]
    let c8r523choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,7),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r523targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] c8r523choice = true := by decide
    refine ⟨c8r523targets, c8r523choice, ?_, checked⟩
    intro S h
    simp only [c8r523targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 18 _ (by rfl)))
  have c8r524_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)] := by
    let c8r524targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)]]
    let c8r524choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0))),((3,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r524targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)] c8r524choice = true := by decide
    refine ⟨c8r524targets, c8r524choice, ?_, checked⟩
    intro S h
    simp only [c8r524targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 24 _ (by rfl)))
  have c8r525_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)] := by
    let c8r525targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)]]
    let c8r525choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,6),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((2,5),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r525targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)] c8r525choice = true := by decide
    refine ⟨c8r525targets, c8r525choice, ?_, checked⟩
    intro S h
    simp only [c8r525targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 28 _ (by rfl)))
  have c8r526_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)] := by
    let c8r526targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)]]
    let c8r526choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,6),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((2,5),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r526targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)] c8r526choice = true := by decide
    refine ⟨c8r526targets, c8r526choice, ?_, checked⟩
    intro S h
    simp only [c8r526targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 31 _ (by rfl)))
  have c8r527_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)] := by
    let c8r527targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)]]
    let c8r527choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,6),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r527targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)] c8r527choice = true := by decide
    refine ⟨c8r527targets, c8r527choice, ?_, checked⟩
    intro S h
    simp only [c8r527targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 1 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r520_closed
  · subst row; exact c8r521_closed
  · subst row; exact c8r522_closed
  · subst row; exact c8r523_closed
  · subst row; exact c8r524_closed
  · subst row; exact c8r525_closed
  · subst row; exact c8r526_closed
  · subst row; exact c8r527_closed
theorem C8R00512G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r528_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)] := by
    let c8r528targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)]]
    let c8r528choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,6),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,6),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r528targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)] c8r528choice = true := by decide
    refine ⟨c8r528targets, c8r528choice, ?_, checked⟩
    intro S h
    simp only [c8r528targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 3 _ (by rfl)))
  have c8r529_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] := by
    let c8r529targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
    let c8r529choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r529targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] c8r529choice = true := by decide
    refine ⟨c8r529targets, c8r529choice, ?_, checked⟩
    intro S h
    simp only [c8r529targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 8 _ (by rfl)))
  have c8r530_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)] := by
    let c8r530targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)]]
    let c8r530choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r530targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)] c8r530choice = true := by decide
    refine ⟨c8r530targets, c8r530choice, ?_, checked⟩
    intro S h
    simp only [c8r530targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 12 _ (by rfl)))
  have c8r531_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)] := by
    let c8r531targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)]]
    let c8r531choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r531targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)] c8r531choice = true := by decide
    refine ⟨c8r531targets, c8r531choice, ?_, checked⟩
    intro S h
    simp only [c8r531targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 15 _ (by rfl)))
  have c8r532_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)] := by
    let c8r532targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)]]
    let c8r532choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,1),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r532targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)] c8r532choice = true := by decide
    refine ⟨c8r532targets, c8r532choice, ?_, checked⟩
    intro S h
    simp only [c8r532targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 18 _ (by rfl)))
  have c8r533_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)] := by
    let c8r533targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)]]
    let c8r533choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,2),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r533targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)] c8r533choice = true := by decide
    refine ⟨c8r533targets, c8r533choice, ?_, checked⟩
    intro S h
    simp only [c8r533targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 21 _ (by rfl)))
  have c8r534_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)] := by
    let c8r534targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)]]
    let c8r534choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r534targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)] c8r534choice = true := by decide
    refine ⟨c8r534targets, c8r534choice, ?_, checked⟩
    intro S h
    simp only [c8r534targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 24 _ (by rfl)))
  have c8r535_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)] := by
    let c8r535targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)]]
    let c8r535choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,5),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r535targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)] c8r535choice = true := by decide
    refine ⟨c8r535targets, c8r535choice, ?_, checked⟩
    intro S h
    simp only [c8r535targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 27 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r528_closed
  · subst row; exact c8r529_closed
  · subst row; exact c8r530_closed
  · subst row; exact c8r531_closed
  · subst row; exact c8r532_closed
  · subst row; exact c8r533_closed
  · subst row; exact c8r534_closed
  · subst row; exact c8r535_closed
theorem C8R00512G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r536_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)] := by
    let c8r536targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)]]
    let c8r536choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r536targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)] c8r536choice = true := by decide
    refine ⟨c8r536targets, c8r536choice, ?_, checked⟩
    intro S h
    simp only [c8r536targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L43_lift _ (familyLookup_sound F9B002L43 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 30 _ (by rfl)))
  have c8r537_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)] := by
    let c8r537targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]]
    let c8r537choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r537targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)] c8r537choice = true := by decide
    refine ⟨c8r537targets, c8r537choice, ?_, checked⟩
    intro S h
    simp only [c8r537targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 1 _ (by rfl)))
  have c8r538_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)] := by
    let c8r538targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)]]
    let c8r538choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r538targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)] c8r538choice = true := by decide
    refine ⟨c8r538targets, c8r538choice, ?_, checked⟩
    intro S h
    simp only [c8r538targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 4 _ (by rfl)))
  have c8r539_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)] := by
    let c8r539targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)]]
    let c8r539choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,6),(11,(0,0))),((3,4),(12,(0,0))),((3,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r539targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)] c8r539choice = true := by decide
    refine ⟨c8r539targets, c8r539choice, ?_, checked⟩
    intro S h
    simp only [c8r539targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 7 _ (by rfl)))
  have c8r540_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)] := by
    let c8r540targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)]]
    let c8r540choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,3),(12,(0,0))),((3,5),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r540targets [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)] c8r540choice = true := by decide
    refine ⟨c8r540targets, c8r540choice, ?_, checked⟩
    intro S h
    simp only [c8r540targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 10 _ (by rfl)))
  have c8r541_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c8r541targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c8r541choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r541targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)] c8r541choice = true := by decide
    refine ⟨c8r541targets, c8r541choice, ?_, checked⟩
    intro S h
    simp only [c8r541targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 15 _ (by rfl)))
  have c8r542_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)] := by
    let c8r542targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)]]
    let c8r542choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r542targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)] c8r542choice = true := by decide
    refine ⟨c8r542targets, c8r542choice, ?_, checked⟩
    intro S h
    simp only [c8r542targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 19 _ (by rfl)))
  have c8r543_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)] := by
    let c8r543targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)]]
    let c8r543choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r543targets [(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)] c8r543choice = true := by decide
    refine ⟨c8r543targets, c8r543choice, ?_, checked⟩
    intro S h
    simp only [c8r543targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L17_lift _ (familyLookup_sound F9B002L17 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 21 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r536_closed
  · subst row; exact c8r537_closed
  · subst row; exact c8r538_closed
  · subst row; exact c8r539_closed
  · subst row; exact c8r540_closed
  · subst row; exact c8r541_closed
  · subst row; exact c8r542_closed
  · subst row; exact c8r543_closed
theorem C8R00512_closed (row : List GridPoint) (h : FamilyMember row F8B000L16) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L16, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00512G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00512G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00512G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00512G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00512G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00512G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00512G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00512G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00512G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00512G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00512G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00512G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00512G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00512G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00512G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00512G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00512G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00512G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00512G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00512G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00512G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00512G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00512G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00512G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00512G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00512G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00512G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00512G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00512G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00512G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00512G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00512G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
