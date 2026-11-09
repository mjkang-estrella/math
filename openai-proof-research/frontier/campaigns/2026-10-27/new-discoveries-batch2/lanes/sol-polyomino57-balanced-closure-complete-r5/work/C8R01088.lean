import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01088G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1088_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)] := by
    let c8r1088targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c8r1088choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1088targets [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)] c8r1088choice = true := by decide
    refine ⟨c8r1088targets, c8r1088choice, ?_, checked⟩
    intro S h
    simp only [c8r1088targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 15 _ (by rfl)))
  have c8r1089_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)] := by
    let c8r1089targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c8r1089choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1089targets [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)] c8r1089choice = true := by decide
    refine ⟨c8r1089targets, c8r1089choice, ?_, checked⟩
    intro S h
    simp only [c8r1089targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 18 _ (by rfl)))
  have c8r1090_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)] := by
    let c8r1090targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c8r1090choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1090targets [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)] c8r1090choice = true := by decide
    refine ⟨c8r1090targets, c8r1090choice, ?_, checked⟩
    intro S h
    simp only [c8r1090targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 21 _ (by rfl)))
  have c8r1091_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)] := by
    let c8r1091targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c8r1091choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1091targets [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)] c8r1091choice = true := by decide
    refine ⟨c8r1091targets, c8r1091choice, ?_, checked⟩
    intro S h
    simp only [c8r1091targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 24 _ (by rfl)))
  have c8r1092_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)] := by
    let c8r1092targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c8r1092choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,4),(10,(0,0))),((5,2),(11,(0,0))),((5,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1092targets [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)] c8r1092choice = true := by decide
    refine ⟨c8r1092targets, c8r1092choice, ?_, checked⟩
    intro S h
    simp only [c8r1092targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 27 _ (by rfl)))
  have c8r1093_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)] := by
    let c8r1093targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c8r1093choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,3),(12,(0,0))),((6,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1093targets [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)] c8r1093choice = true := by decide
    refine ⟨c8r1093targets, c8r1093choice, ?_, checked⟩
    intro S h
    simp only [c8r1093targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 30 _ (by rfl)))
  have c8r1094_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c8r1094targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c8r1094choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1094targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)] c8r1094choice = true := by decide
    refine ⟨c8r1094targets, c8r1094choice, ?_, checked⟩
    intro S h
    simp only [c8r1094targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 3 _ (by rfl)))
  have c8r1095_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c8r1095targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c8r1095choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1095targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)] c8r1095choice = true := by decide
    refine ⟨c8r1095targets, c8r1095choice, ?_, checked⟩
    intro S h
    simp only [c8r1095targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 5 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1088_closed
  · subst row; exact c8r1089_closed
  · subst row; exact c8r1090_closed
  · subst row; exact c8r1091_closed
  · subst row; exact c8r1092_closed
  · subst row; exact c8r1093_closed
  · subst row; exact c8r1094_closed
  · subst row; exact c8r1095_closed
theorem C8R01088G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1096_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c8r1096targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c8r1096choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1096targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)] c8r1096choice = true := by decide
    refine ⟨c8r1096targets, c8r1096choice, ?_, checked⟩
    intro S h
    simp only [c8r1096targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 7 _ (by rfl)))
  have c8r1097_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c8r1097targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c8r1097choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,4),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1097targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)] c8r1097choice = true := by decide
    refine ⟨c8r1097targets, c8r1097choice, ?_, checked⟩
    intro S h
    simp only [c8r1097targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 11 _ (by rfl)))
  have c8r1098_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)] := by
    let c8r1098targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c8r1098choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1098targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)] c8r1098choice = true := by decide
    refine ⟨c8r1098targets, c8r1098choice, ?_, checked⟩
    intro S h
    simp only [c8r1098targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 14 _ (by rfl)))
  have c8r1099_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)] := by
    let c8r1099targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c8r1099choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,3),(12,(0,0))),((6,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1099targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)] c8r1099choice = true := by decide
    refine ⟨c8r1099targets, c8r1099choice, ?_, checked⟩
    intro S h
    simp only [c8r1099targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 16 _ (by rfl)))
  have c8r1100_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c8r1100targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c8r1100choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1100targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)] c8r1100choice = true := by decide
    refine ⟨c8r1100targets, c8r1100choice, ?_, checked⟩
    intro S h
    simp only [c8r1100targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 19 _ (by rfl)))
  have c8r1101_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)] := by
    let c8r1101targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c8r1101choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,3),(12,(0,0))),((6,1),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1101targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)] c8r1101choice = true := by decide
    refine ⟨c8r1101targets, c8r1101choice, ?_, checked⟩
    intro S h
    simp only [c8r1101targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 22 _ (by rfl)))
  have c8r1102_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)] := by
    let c8r1102targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c8r1102choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,2),(14,(0,0))),((7,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1102targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)] c8r1102choice = true := by decide
    refine ⟨c8r1102targets, c8r1102choice, ?_, checked⟩
    intro S h
    simp only [c8r1102targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 25 _ (by rfl)))
  have c8r1103_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c8r1103targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1103choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,-1),(10,(0,1))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1103targets [(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)] c8r1103choice = true := by decide
    refine ⟨c8r1103targets, c8r1103choice, ?_, checked⟩
    intro S h
    simp only [c8r1103targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 30 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1096_closed
  · subst row; exact c8r1097_closed
  · subst row; exact c8r1098_closed
  · subst row; exact c8r1099_closed
  · subst row; exact c8r1100_closed
  · subst row; exact c8r1101_closed
  · subst row; exact c8r1102_closed
  · subst row; exact c8r1103_closed
theorem C8R01088G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1104_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r1104targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r1104choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1104targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)] c8r1104choice = true := by decide
    refine ⟨c8r1104targets, c8r1104choice, ?_, checked⟩
    intro S h
    simp only [c8r1104targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 3 _ (by rfl)))
  have c8r1105_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r1105targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r1105choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1105targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)] c8r1105choice = true := by decide
    refine ⟨c8r1105targets, c8r1105choice, ?_, checked⟩
    intro S h
    simp only [c8r1105targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 6 _ (by rfl)))
  have c8r1106_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r1106targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r1106choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1106targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)] c8r1106choice = true := by decide
    refine ⟨c8r1106targets, c8r1106choice, ?_, checked⟩
    intro S h
    simp only [c8r1106targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 8 _ (by rfl)))
  have c8r1107_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c8r1107targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c8r1107choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1107targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] c8r1107choice = true := by decide
    refine ⟨c8r1107targets, c8r1107choice, ?_, checked⟩
    intro S h
    simp only [c8r1107targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 10 _ (by rfl)))
  have c8r1108_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r1108targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r1108choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,-1),(10,(0,1))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1108targets [(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)] c8r1108choice = true := by decide
    refine ⟨c8r1108targets, c8r1108choice, ?_, checked⟩
    intro S h
    simp only [c8r1108targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L62_lift _ (familyLookup_sound F9B002L62 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 17 _ (by rfl)))
  have c8r1109_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c8r1109targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c8r1109choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,-1),(10,(0,1))),((3,5),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0))),((4,3),(15,(0,0))),((4,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1109targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)] c8r1109choice = true := by decide
    refine ⟨c8r1109targets, c8r1109choice, ?_, checked⟩
    intro S h
    simp only [c8r1109targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L63_lift _ (familyLookup_sound F9B002L63 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 24 _ (by rfl)))
  have c8r1110_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c8r1110targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c8r1110choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0))),((5,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1110targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)] c8r1110choice = true := by decide
    refine ⟨c8r1110targets, c8r1110choice, ?_, checked⟩
    intro S h
    simp only [c8r1110targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L63_lift _ (familyLookup_sound F9B002L63 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 28 _ (by rfl)))
  have c8r1111_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c8r1111targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c8r1111choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1111targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)] c8r1111choice = true := by decide
    refine ⟨c8r1111targets, c8r1111choice, ?_, checked⟩
    intro S h
    simp only [c8r1111targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L63_lift _ (familyLookup_sound F9B002L63 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 31 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1104_closed
  · subst row; exact c8r1105_closed
  · subst row; exact c8r1106_closed
  · subst row; exact c8r1107_closed
  · subst row; exact c8r1108_closed
  · subst row; exact c8r1109_closed
  · subst row; exact c8r1110_closed
  · subst row; exact c8r1111_closed
theorem C8R01088G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1112_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c8r1112targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c8r1112choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1112targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)] c8r1112choice = true := by decide
    refine ⟨c8r1112targets, c8r1112choice, ?_, checked⟩
    intro S h
    simp only [c8r1112targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L63_lift _ (familyLookup_sound F9B002L63 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 1 _ (by rfl)))
  have c8r1113_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c8r1113targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c8r1113choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,4),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1113targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)] c8r1113choice = true := by decide
    refine ⟨c8r1113targets, c8r1113choice, ?_, checked⟩
    intro S h
    simp only [c8r1113targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L63_lift _ (familyLookup_sound F9B002L63 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 3 _ (by rfl)))
  have c8r1114_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)] := by
    let c8r1114targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c8r1114choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1114targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)] c8r1114choice = true := by decide
    refine ⟨c8r1114targets, c8r1114choice, ?_, checked⟩
    intro S h
    simp only [c8r1114targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 6 _ (by rfl)))
  have c8r1115_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)] := by
    let c8r1115targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)]]
    let c8r1115choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,0),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1115targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)] c8r1115choice = true := by decide
    refine ⟨c8r1115targets, c8r1115choice, ?_, checked⟩
    intro S h
    simp only [c8r1115targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 9 _ (by rfl)))
  have c8r1116_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)] := by
    let c8r1116targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)]]
    let c8r1116choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((5,-1),(13,(0,1))),((5,1),(14,(0,0))),((6,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1116targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)] c8r1116choice = true := by decide
    refine ⟨c8r1116targets, c8r1116choice, ?_, checked⟩
    intro S h
    simp only [c8r1116targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L6_lift _ (familyLookup_sound F9B003L6 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 11 _ (by rfl)))
  have c8r1117_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)] := by
    let c8r1117targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c8r1117choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1117targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)] c8r1117choice = true := by decide
    refine ⟨c8r1117targets, c8r1117choice, ?_, checked⟩
    intro S h
    simp only [c8r1117targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 14 _ (by rfl)))
  have c8r1118_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)] := by
    let c8r1118targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c8r1118choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1118targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)] c8r1118choice = true := by decide
    refine ⟨c8r1118targets, c8r1118choice, ?_, checked⟩
    intro S h
    simp only [c8r1118targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 17 _ (by rfl)))
  have c8r1119_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)] := by
    let c8r1119targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c8r1119choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,4),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1119targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)] c8r1119choice = true := by decide
    refine ⟨c8r1119targets, c8r1119choice, ?_, checked⟩
    intro S h
    simp only [c8r1119targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L54_lift _ (familyLookup_sound F9B001L54 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L53_lift _ (familyLookup_sound F9B000L53 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L0_lift _ (familyLookup_sound F9B003L0 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L4_lift _ (familyLookup_sound F9B003L4 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 20 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1112_closed
  · subst row; exact c8r1113_closed
  · subst row; exact c8r1114_closed
  · subst row; exact c8r1115_closed
  · subst row; exact c8r1116_closed
  · subst row; exact c8r1117_closed
  · subst row; exact c8r1118_closed
  · subst row; exact c8r1119_closed
theorem C8R01088_closed (row : List GridPoint) (h : FamilyMember row F8B000L34) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L34, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01088G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01088G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01088G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01088G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01088G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01088G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01088G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01088G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01088G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01088G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01088G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01088G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01088G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01088G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01088G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01088G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01088G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01088G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01088G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01088G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01088G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01088G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01088G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01088G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01088G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01088G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01088G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01088G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01088G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01088G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01088G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01088G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
