import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01120G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1120_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)] := by
    let c8r1120targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c8r1120choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,3),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1120targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)] c8r1120choice = true := by decide
    refine ⟨c8r1120targets, c8r1120choice, ?_, checked⟩
    intro S h
    simp only [c8r1120targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 23 _ (by rfl)))
  have c8r1121_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)] := by
    let c8r1121targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c8r1121choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1121targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)] c8r1121choice = true := by decide
    refine ⟨c8r1121targets, c8r1121choice, ?_, checked⟩
    intro S h
    simp only [c8r1121targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 28 _ (by rfl)))
  have c8r1122_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)] := by
    let c8r1122targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c8r1122choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1122targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)] c8r1122choice = true := by decide
    refine ⟨c8r1122targets, c8r1122choice, ?_, checked⟩
    intro S h
    simp only [c8r1122targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 30 _ (by rfl)))
  have c8r1123_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)] := by
    let c8r1123targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c8r1123choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1123targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)] c8r1123choice = true := by decide
    refine ⟨c8r1123targets, c8r1123choice, ?_, checked⟩
    intro S h
    simp only [c8r1123targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 0 _ (by rfl)))
  have c8r1124_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)] := by
    let c8r1124targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)]]
    let c8r1124choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1124targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)] c8r1124choice = true := by decide
    refine ⟨c8r1124targets, c8r1124choice, ?_, checked⟩
    intro S h
    simp only [c8r1124targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 3 _ (by rfl)))
  have c8r1125_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)] := by
    let c8r1125targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)]]
    let c8r1125choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,-1),(13,(0,1))),((6,1),(14,(0,0))),((7,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1125targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)] c8r1125choice = true := by decide
    refine ⟨c8r1125targets, c8r1125choice, ?_, checked⟩
    intro S h
    simp only [c8r1125targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 5 _ (by rfl)))
  have c8r1126_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)] := by
    let c8r1126targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c8r1126choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,4),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1126targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)] c8r1126choice = true := by decide
    refine ⟨c8r1126targets, c8r1126choice, ?_, checked⟩
    intro S h
    simp only [c8r1126targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 9 _ (by rfl)))
  have c8r1127_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)] := by
    let c8r1127targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c8r1127choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1127targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)] c8r1127choice = true := by decide
    refine ⟨c8r1127targets, c8r1127choice, ?_, checked⟩
    intro S h
    simp only [c8r1127targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 12 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1120_closed
  · subst row; exact c8r1121_closed
  · subst row; exact c8r1122_closed
  · subst row; exact c8r1123_closed
  · subst row; exact c8r1124_closed
  · subst row; exact c8r1125_closed
  · subst row; exact c8r1126_closed
  · subst row; exact c8r1127_closed
theorem C8R01120G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1128_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)] := by
    let c8r1128targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c8r1128choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,3),(12,(0,0))),((6,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1128targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)] c8r1128choice = true := by decide
    refine ⟨c8r1128targets, c8r1128choice, ?_, checked⟩
    intro S h
    simp only [c8r1128targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 14 _ (by rfl)))
  have c8r1129_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)] := by
    let c8r1129targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c8r1129choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1129targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)] c8r1129choice = true := by decide
    refine ⟨c8r1129targets, c8r1129choice, ?_, checked⟩
    intro S h
    simp only [c8r1129targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 17 _ (by rfl)))
  have c8r1130_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)] := by
    let c8r1130targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c8r1130choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,3),(12,(0,0))),((6,1),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1130targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)] c8r1130choice = true := by decide
    refine ⟨c8r1130targets, c8r1130choice, ?_, checked⟩
    intro S h
    simp only [c8r1130targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 20 _ (by rfl)))
  have c8r1131_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)] := by
    let c8r1131targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c8r1131choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,2),(14,(0,0))),((7,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1131targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)] c8r1131choice = true := by decide
    refine ⟨c8r1131targets, c8r1131choice, ?_, checked⟩
    intro S h
    simp only [c8r1131targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 23 _ (by rfl)))
  have c8r1132_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)] := by
    let c8r1132targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c8r1132choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,3),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1132targets [(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)] c8r1132choice = true := by decide
    refine ⟨c8r1132targets, c8r1132choice, ?_, checked⟩
    intro S h
    simp only [c8r1132targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 28 _ (by rfl)))
  have c8r1133_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)] := by
    let c8r1133targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c8r1133choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,4),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0))),((5,2),(15,(0,0))),((5,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1133targets [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)] c8r1133choice = true := by decide
    refine ⟨c8r1133targets, c8r1133choice, ?_, checked⟩
    intro S h
    simp only [c8r1133targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 2 _ (by rfl)))
  have c8r1134_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)] := by
    let c8r1134targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c8r1134choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((5,2),(14,(0,0))),((6,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1134targets [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)] c8r1134choice = true := by decide
    refine ⟨c8r1134targets, c8r1134choice, ?_, checked⟩
    intro S h
    simp only [c8r1134targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 5 _ (by rfl)))
  have c8r1135_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)] := by
    let c8r1135targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c8r1135choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1135targets [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)] c8r1135choice = true := by decide
    refine ⟨c8r1135targets, c8r1135choice, ?_, checked⟩
    intro S h
    simp only [c8r1135targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 7 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1128_closed
  · subst row; exact c8r1129_closed
  · subst row; exact c8r1130_closed
  · subst row; exact c8r1131_closed
  · subst row; exact c8r1132_closed
  · subst row; exact c8r1133_closed
  · subst row; exact c8r1134_closed
  · subst row; exact c8r1135_closed
theorem C8R01120G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1136_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)] := by
    let c8r1136targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c8r1136choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,3),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1136targets [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)] c8r1136choice = true := by decide
    refine ⟨c8r1136targets, c8r1136choice, ?_, checked⟩
    intro S h
    simp only [c8r1136targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 9 _ (by rfl)))
  have c8r1137_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)] := by
    let c8r1137targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,1)]]
    let c8r1137choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1137targets [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)] c8r1137choice = true := by decide
    refine ⟨c8r1137targets, c8r1137choice, ?_, checked⟩
    intro S h
    simp only [c8r1137targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 12 _ (by rfl)))
  have c8r1138_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)] := by
    let c8r1138targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(7,0)]]
    let c8r1138choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,-1),(13,(0,1))),((6,1),(14,(0,0))),((7,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1138targets [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)] c8r1138choice = true := by decide
    refine ⟨c8r1138targets, c8r1138choice, ?_, checked⟩
    intro S h
    simp only [c8r1138targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 14 _ (by rfl)))
  have c8r1139_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)] := by
    let c8r1139targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,2)]]
    let c8r1139choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,3),(12,(0,0))),((6,1),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1139targets [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)] c8r1139choice = true := by decide
    refine ⟨c8r1139targets, c8r1139choice, ?_, checked⟩
    intro S h
    simp only [c8r1139targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 17 _ (by rfl)))
  have c8r1140_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)] := by
    let c8r1140targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(7,1)]]
    let c8r1140choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,2),(14,(0,0))),((7,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1140targets [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)] c8r1140choice = true := by decide
    refine ⟨c8r1140targets, c8r1140choice, ?_, checked⟩
    intro S h
    simp only [c8r1140targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L5_lift _ (familyLookup_sound F9B003L5 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 20 _ (by rfl)))
  have c8r1141_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)] := by
    let c8r1141targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,0)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,2)]]
    let c8r1141choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,3),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0))),((6,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1141targets [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)] c8r1141choice = true := by decide
    refine ⟨c8r1141targets, c8r1141choice, ?_, checked⟩
    intro S h
    simp only [c8r1141targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 25 _ (by rfl)))
  have c8r1142_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)] := by
    let c8r1142targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0),(7,0)]]
    let c8r1142choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,-1),(13,(0,1))),((6,1),(14,(0,0))),((7,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1142targets [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)] c8r1142choice = true := by decide
    refine ⟨c8r1142targets, c8r1142choice, ?_, checked⟩
    intro S h
    simp only [c8r1142targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 27 _ (by rfl)))
  have c8r1143_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)] := by
    let c8r1143targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1),(7,1)]]
    let c8r1143choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,2),(14,(0,0))),((7,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1143targets [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)] c8r1143choice = true := by decide
    refine ⟨c8r1143targets, c8r1143choice, ?_, checked⟩
    intro S h
    simp only [c8r1143targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 29 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1136_closed
  · subst row; exact c8r1137_closed
  · subst row; exact c8r1138_closed
  · subst row; exact c8r1139_closed
  · subst row; exact c8r1140_closed
  · subst row; exact c8r1141_closed
  · subst row; exact c8r1142_closed
  · subst row; exact c8r1143_closed
theorem C8R01120G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1144_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)] := by
    let c8r1144targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1),(7,0)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1),(7,1)]]
    let c8r1144choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,-1),(13,(0,1))),((6,2),(14,(0,0))),((7,0),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1144targets [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)] c8r1144choice = true := by decide
    refine ⟨c8r1144targets, c8r1144choice, ?_, checked⟩
    intro S h
    simp only [c8r1144targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 0 _ (by rfl)))
  have c8r1145_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)] := by
    let c8r1145targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0),(8,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1),(7,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,0),(7,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0),(7,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0),(8,0)]]
    let c8r1145choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,-1),(13,(0,1))),((6,1),(14,(0,0))),((7,-1),(15,(0,1))),((7,1),(16,(0,0))),((8,0),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1145targets [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)] c8r1145choice = true := by decide
    refine ⟨c8r1145targets, c8r1145choice, ?_, checked⟩
    intro S h
    simp only [c8r1145targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L7_lift _ (familyLookup_sound F9B003L7 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 2 _ (by rfl)))
  have c8r1146_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1)] := by
    let c8r1146targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1)],[(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,1)]]
    let c8r1146choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((-1,5),(4,(1,0))),((-1,6),(5,(1,0))),((0,0),(6,(0,0))),((0,7),(7,(0,0))),((1,-1),(8,(0,1))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((1,6),(13,(0,0))),((2,0),(14,(0,0))),((2,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1146targets [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1)] c8r1146choice = true := by decide
    refine ⟨c8r1146targets, c8r1146choice, ?_, checked⟩
    intro S h
    simp only [c8r1146targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 23 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 20 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 16 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 13 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L53_lift _ (familyLookup_sound F9B004L53 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 10 _ (by rfl)))
  have c8r1147_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)] := by
    let c8r1147targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2)]]
    let c8r1147choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((-1,5),(4,(1,0))),((0,0),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,1),(12,(0,0))),((2,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1147targets [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)] c8r1147choice = true := by decide
    refine ⟨c8r1147targets, c8r1147choice, ?_, checked⟩
    intro S h
    simp only [c8r1147targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 24 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 21 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 17 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 17 _ (by rfl)))
  have c8r1148_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)] := by
    let c8r1148targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,3)]]
    let c8r1148choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((-1,5),(4,(1,0))),((0,0),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,1),(12,(0,0))),((2,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1148targets [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)] c8r1148choice = true := by decide
    refine ⟨c8r1148targets, c8r1148choice, ?_, checked⟩
    intro S h
    simp only [c8r1148targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 25 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 22 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 18 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 22 _ (by rfl)))
  have c8r1149_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)] := by
    let c8r1149targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4)]]
    let c8r1149choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((-1,5),(4,(1,0))),((0,0),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,1),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1149targets [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)] c8r1149choice = true := by decide
    refine ⟨c8r1149targets, c8r1149choice, ?_, checked⟩
    intro S h
    simp only [c8r1149targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 26 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 23 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 19 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 26 _ (by rfl)))
  have c8r1150_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5)] := by
    let c8r1150targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,5)]]
    let c8r1150choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((-1,5),(4,(1,0))),((0,0),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((1,6),(11,(0,0))),((2,0),(12,(0,0))),((2,1),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1150targets [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5)] c8r1150choice = true := by decide
    refine ⟨c8r1150targets, c8r1150choice, ?_, checked⟩
    intro S h
    simp only [c8r1150targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 27 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 24 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 20 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 30 _ (by rfl)))
  have c8r1151_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0)] := by
    let c8r1151targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,0)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,0)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(3,0)]]
    let c8r1151choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((-1,5),(4,(1,0))),((0,0),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((1,5),(11,(0,0))),((2,-1),(12,(0,1))),((2,1),(13,(0,0))),((3,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1151targets [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0)] c8r1151choice = true := by decide
    refine ⟨c8r1151targets, c8r1151choice, ?_, checked⟩
    intro S h
    simp only [c8r1151targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L42_lift _ (familyLookup_sound F9B003L42 [] 28 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 25 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 21 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L8_lift _ (familyLookup_sound F9B003L8 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 0 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1144_closed
  · subst row; exact c8r1145_closed
  · subst row; exact c8r1146_closed
  · subst row; exact c8r1147_closed
  · subst row; exact c8r1148_closed
  · subst row; exact c8r1149_closed
  · subst row; exact c8r1150_closed
  · subst row; exact c8r1151_closed
theorem C8R01120_closed (row : List GridPoint) (h : FamilyMember row F8B000L35) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L35, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01120G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01120G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01120G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01120G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01120G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01120G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01120G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01120G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01120G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01120G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01120G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01120G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01120G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01120G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01120G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01120G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01120G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01120G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01120G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01120G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01120G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01120G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01120G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01120G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01120G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01120G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01120G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01120G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01120G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01120G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01120G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01120G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
