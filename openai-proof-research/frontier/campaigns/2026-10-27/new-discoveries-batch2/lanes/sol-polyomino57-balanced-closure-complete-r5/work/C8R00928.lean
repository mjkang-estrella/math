import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00928G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r928_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)] := by
    let c8r928targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c8r928choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r928targets [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)] c8r928choice = true := by decide
    refine ⟨c8r928targets, c8r928choice, ?_, checked⟩
    intro S h
    simp only [c8r928targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 8 _ (by rfl)))
  have c8r929_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)] := by
    let c8r929targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c8r929choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r929targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)] c8r929choice = true := by decide
    refine ⟨c8r929targets, c8r929choice, ?_, checked⟩
    intro S h
    simp only [c8r929targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 13 _ (by rfl)))
  have c8r930_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)] := by
    let c8r930targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c8r930choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r930targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)] c8r930choice = true := by decide
    refine ⟨c8r930targets, c8r930choice, ?_, checked⟩
    intro S h
    simp only [c8r930targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 15 _ (by rfl)))
  have c8r931_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)] := by
    let c8r931targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c8r931choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r931targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)] c8r931choice = true := by decide
    refine ⟨c8r931targets, c8r931choice, ?_, checked⟩
    intro S h
    simp only [c8r931targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L35_lift _ (familyLookup_sound F9B002L35 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 17 _ (by rfl)))
  have c8r932_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)] := by
    let c8r932targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)]]
    let c8r932choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r932targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)] c8r932choice = true := by decide
    refine ⟨c8r932targets, c8r932choice, ?_, checked⟩
    intro S h
    simp only [c8r932targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 20 _ (by rfl)))
  have c8r933_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)] := by
    let c8r933targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)]]
    let c8r933choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r933targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)] c8r933choice = true := by decide
    refine ⟨c8r933targets, c8r933choice, ?_, checked⟩
    intro S h
    simp only [c8r933targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 22 _ (by rfl)))
  have c8r934_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)] := by
    let c8r934targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c8r934choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r934targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)] c8r934choice = true := by decide
    refine ⟨c8r934targets, c8r934choice, ?_, checked⟩
    intro S h
    simp only [c8r934targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 26 _ (by rfl)))
  have c8r935_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)] := by
    let c8r935targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c8r935choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r935targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)] c8r935choice = true := by decide
    refine ⟨c8r935targets, c8r935choice, ?_, checked⟩
    intro S h
    simp only [c8r935targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 29 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r928_closed
  · subst row; exact c8r929_closed
  · subst row; exact c8r930_closed
  · subst row; exact c8r931_closed
  · subst row; exact c8r932_closed
  · subst row; exact c8r933_closed
  · subst row; exact c8r934_closed
  · subst row; exact c8r935_closed
theorem C8R00928G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r936_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)] := by
    let c8r936targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c8r936choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r936targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)] c8r936choice = true := by decide
    refine ⟨c8r936targets, c8r936choice, ?_, checked⟩
    intro S h
    simp only [c8r936targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 31 _ (by rfl)))
  have c8r937_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)] := by
    let c8r937targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c8r937choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r937targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)] c8r937choice = true := by decide
    refine ⟨c8r937targets, c8r937choice, ?_, checked⟩
    intro S h
    simp only [c8r937targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 2 _ (by rfl)))
  have c8r938_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)] := by
    let c8r938targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c8r938choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r938targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)] c8r938choice = true := by decide
    refine ⟨c8r938targets, c8r938choice, ?_, checked⟩
    intro S h
    simp only [c8r938targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 5 _ (by rfl)))
  have c8r939_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)] := by
    let c8r939targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c8r939choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r939targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)] c8r939choice = true := by decide
    refine ⟨c8r939targets, c8r939choice, ?_, checked⟩
    intro S h
    simp only [c8r939targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 8 _ (by rfl)))
  have c8r940_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r940targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r940choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r940targets [(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2)] c8r940choice = true := by decide
    refine ⟨c8r940targets, c8r940choice, ?_, checked⟩
    intro S h
    simp only [c8r940targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 13 _ (by rfl)))
  have c8r941_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r941targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r941choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r941targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3)] c8r941choice = true := by decide
    refine ⟨c8r941targets, c8r941choice, ?_, checked⟩
    intro S h
    simp only [c8r941targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 19 _ (by rfl)))
  have c8r942_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r942targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r942choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r942targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)] c8r942choice = true := by decide
    refine ⟨c8r942targets, c8r942choice, ?_, checked⟩
    intro S h
    simp only [c8r942targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 22 _ (by rfl)))
  have c8r943_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r943targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r943choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r943targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)] c8r943choice = true := by decide
    refine ⟨c8r943targets, c8r943choice, ?_, checked⟩
    intro S h
    simp only [c8r943targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 24 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r936_closed
  · subst row; exact c8r937_closed
  · subst row; exact c8r938_closed
  · subst row; exact c8r939_closed
  · subst row; exact c8r940_closed
  · subst row; exact c8r941_closed
  · subst row; exact c8r942_closed
  · subst row; exact c8r943_closed
theorem C8R00928G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r944_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2)] := by
    let c8r944targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c8r944choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r944targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2)] c8r944choice = true := by decide
    refine ⟨c8r944targets, c8r944choice, ?_, checked⟩
    intro S h
    simp only [c8r944targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 26 _ (by rfl)))
  have c8r945_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)] := by
    let c8r945targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c8r945choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r945targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)] c8r945choice = true := by decide
    refine ⟨c8r945targets, c8r945choice, ?_, checked⟩
    intro S h
    simp only [c8r945targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 29 _ (by rfl)))
  have c8r946_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)] := by
    let c8r946targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c8r946choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r946targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)] c8r946choice = true := by decide
    refine ⟨c8r946targets, c8r946choice, ?_, checked⟩
    intro S h
    simp only [c8r946targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 31 _ (by rfl)))
  have c8r947_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2)] := by
    let c8r947targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c8r947choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r947targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2)] c8r947choice = true := by decide
    refine ⟨c8r947targets, c8r947choice, ?_, checked⟩
    intro S h
    simp only [c8r947targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 2 _ (by rfl)))
  have c8r948_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1)] := by
    let c8r948targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c8r948choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r948targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1)] c8r948choice = true := by decide
    refine ⟨c8r948targets, c8r948choice, ?_, checked⟩
    intro S h
    simp only [c8r948targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 5 _ (by rfl)))
  have c8r949_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2)] := by
    let c8r949targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)]]
    let c8r949choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r949targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2)] c8r949choice = true := by decide
    refine ⟨c8r949targets, c8r949choice, ?_, checked⟩
    intro S h
    simp only [c8r949targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 10 _ (by rfl)))
  have c8r950_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)] := by
    let c8r950targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)]]
    let c8r950choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r950targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)] c8r950choice = true := by decide
    refine ⟨c8r950targets, c8r950choice, ?_, checked⟩
    intro S h
    simp only [c8r950targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 12 _ (by rfl)))
  have c8r951_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1)] := by
    let c8r951targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)]]
    let c8r951choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r951targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1)] c8r951choice = true := by decide
    refine ⟨c8r951targets, c8r951choice, ?_, checked⟩
    intro S h
    simp only [c8r951targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 14 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r944_closed
  · subst row; exact c8r945_closed
  · subst row; exact c8r946_closed
  · subst row; exact c8r947_closed
  · subst row; exact c8r948_closed
  · subst row; exact c8r949_closed
  · subst row; exact c8r950_closed
  · subst row; exact c8r951_closed
theorem C8R00928G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r952_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1)] := by
    let c8r952targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)]]
    let c8r952choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r952targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1)] c8r952choice = true := by decide
    refine ⟨c8r952targets, c8r952choice, ?_, checked⟩
    intro S h
    simp only [c8r952targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 17 _ (by rfl)))
  have c8r953_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0)] := by
    let c8r953targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)]]
    let c8r953choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,-1),(13,(0,1))),((6,1),(14,(0,0))),((7,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r953targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0)] c8r953choice = true := by decide
    refine ⟨c8r953targets, c8r953choice, ?_, checked⟩
    intro S h
    simp only [c8r953targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L54_lift _ (familyLookup_sound F9B002L54 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L55_lift _ (familyLookup_sound F9B002L55 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 19 _ (by rfl)))
  have c8r954_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c8r954targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c8r954choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,6),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r954targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)] c8r954choice = true := by decide
    refine ⟨c8r954targets, c8r954choice, ?_, checked⟩
    intro S h
    simp only [c8r954targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 25 _ (by rfl)))
  have c8r955_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)] := by
    let c8r955targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]
    let c8r955choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r955targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)] c8r955choice = true := by decide
    refine ⟨c8r955targets, c8r955choice, ?_, checked⟩
    intro S h
    simp only [c8r955targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 30 _ (by rfl)))
  have c8r956_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)] := by
    let c8r956targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c8r956choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r956targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)] c8r956choice = true := by decide
    refine ⟨c8r956targets, c8r956choice, ?_, checked⟩
    intro S h
    simp only [c8r956targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 1 _ (by rfl)))
  have c8r957_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)] := by
    let c8r957targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c8r957choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r957targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)] c8r957choice = true := by decide
    refine ⟨c8r957targets, c8r957choice, ?_, checked⟩
    intro S h
    simp only [c8r957targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 3 _ (by rfl)))
  have c8r958_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c8r958targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c8r958choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,5),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r958targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)] c8r958choice = true := by decide
    refine ⟨c8r958targets, c8r958choice, ?_, checked⟩
    intro S h
    simp only [c8r958targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 5 _ (by rfl)))
  have c8r959_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c8r959targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c8r959choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r959targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)] c8r959choice = true := by decide
    refine ⟨c8r959targets, c8r959choice, ?_, checked⟩
    intro S h
    simp only [c8r959targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 9 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r952_closed
  · subst row; exact c8r953_closed
  · subst row; exact c8r954_closed
  · subst row; exact c8r955_closed
  · subst row; exact c8r956_closed
  · subst row; exact c8r957_closed
  · subst row; exact c8r958_closed
  · subst row; exact c8r959_closed
theorem C8R00928_closed (row : List GridPoint) (h : FamilyMember row F8B000L29) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L29, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00928G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00928G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00928G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00928G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00928G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00928G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00928G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00928G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00928G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00928G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00928G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00928G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00928G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00928G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00928G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00928G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00928G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00928G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00928G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00928G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00928G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00928G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00928G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00928G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00928G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00928G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00928G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00928G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00928G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00928G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00928G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00928G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
