import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01056G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1056_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)] := by
    let c8r1056targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)]]
    let c8r1056choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1056targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)] c8r1056choice = true := by decide
    refine ⟨c8r1056targets, c8r1056choice, ?_, checked⟩
    intro S h
    simp only [c8r1056targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L1_lift _ (familyLookup_sound F9B003L1 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 12 _ (by rfl)))
  have c8r1057_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)] := by
    let c8r1057targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)]]
    let c8r1057choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1057targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)] c8r1057choice = true := by decide
    refine ⟨c8r1057targets, c8r1057choice, ?_, checked⟩
    intro S h
    simp only [c8r1057targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 15 _ (by rfl)))
  have c8r1058_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)] := by
    let c8r1058targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)]]
    let c8r1058choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,-1),(13,(0,1))),((5,1),(14,(0,0))),((6,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1058targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)] c8r1058choice = true := by decide
    refine ⟨c8r1058targets, c8r1058choice, ?_, checked⟩
    intro S h
    simp only [c8r1058targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 17 _ (by rfl)))
  have c8r1059_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)] := by
    let c8r1059targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c8r1059choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1059targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)] c8r1059choice = true := by decide
    refine ⟨c8r1059targets, c8r1059choice, ?_, checked⟩
    intro S h
    simp only [c8r1059targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 21 _ (by rfl)))
  have c8r1060_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)] := by
    let c8r1060targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c8r1060choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1060targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)] c8r1060choice = true := by decide
    refine ⟨c8r1060targets, c8r1060choice, ?_, checked⟩
    intro S h
    simp only [c8r1060targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 24 _ (by rfl)))
  have c8r1061_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)] := by
    let c8r1061targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c8r1061choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1061targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)] c8r1061choice = true := by decide
    refine ⟨c8r1061targets, c8r1061choice, ?_, checked⟩
    intro S h
    simp only [c8r1061targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 26 _ (by rfl)))
  have c8r1062_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c8r1062targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c8r1062choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1062targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)] c8r1062choice = true := by decide
    refine ⟨c8r1062targets, c8r1062choice, ?_, checked⟩
    intro S h
    simp only [c8r1062targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 29 _ (by rfl)))
  have c8r1063_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)] := by
    let c8r1063targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)]]
    let c8r1063choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1063targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)] c8r1063choice = true := by decide
    refine ⟨c8r1063targets, c8r1063choice, ?_, checked⟩
    intro S h
    simp only [c8r1063targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 0 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1056_closed
  · subst row; exact c8r1057_closed
  · subst row; exact c8r1058_closed
  · subst row; exact c8r1059_closed
  · subst row; exact c8r1060_closed
  · subst row; exact c8r1061_closed
  · subst row; exact c8r1062_closed
  · subst row; exact c8r1063_closed
theorem C8R01056G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1064_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)] := by
    let c8r1064targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)]]
    let c8r1064choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1064targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)] c8r1064choice = true := by decide
    refine ⟨c8r1064targets, c8r1064choice, ?_, checked⟩
    intro S h
    simp only [c8r1064targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 3 _ (by rfl)))
  have c8r1065_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)] := by
    let c8r1065targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c8r1065choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,5),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1065targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)] c8r1065choice = true := by decide
    refine ⟨c8r1065targets, c8r1065choice, ?_, checked⟩
    intro S h
    simp only [c8r1065targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 7 _ (by rfl)))
  have c8r1066_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)] := by
    let c8r1066targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c8r1066choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1066targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)] c8r1066choice = true := by decide
    refine ⟨c8r1066targets, c8r1066choice, ?_, checked⟩
    intro S h
    simp only [c8r1066targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 10 _ (by rfl)))
  have c8r1067_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)] := by
    let c8r1067targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c8r1067choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1067targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)] c8r1067choice = true := by decide
    refine ⟨c8r1067targets, c8r1067choice, ?_, checked⟩
    intro S h
    simp only [c8r1067targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 12 _ (by rfl)))
  have c8r1068_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)] := by
    let c8r1068targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c8r1068choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1068targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)] c8r1068choice = true := by decide
    refine ⟨c8r1068targets, c8r1068choice, ?_, checked⟩
    intro S h
    simp only [c8r1068targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 16 _ (by rfl)))
  have c8r1069_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)] := by
    let c8r1069targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c8r1069choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,4),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1069targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)] c8r1069choice = true := by decide
    refine ⟨c8r1069targets, c8r1069choice, ?_, checked⟩
    intro S h
    simp only [c8r1069targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L51_lift _ (familyLookup_sound F9B000L51 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 19 _ (by rfl)))
  have c8r1070_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)] := by
    let c8r1070targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c8r1070choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,3),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1070targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)] c8r1070choice = true := by decide
    refine ⟨c8r1070targets, c8r1070choice, ?_, checked⟩
    intro S h
    simp only [c8r1070targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 22 _ (by rfl)))
  have c8r1071_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)] := by
    let c8r1071targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c8r1071choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1071targets [(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)] c8r1071choice = true := by decide
    refine ⟨c8r1071targets, c8r1071choice, ?_, checked⟩
    intro S h
    simp only [c8r1071targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L44_lift _ (familyLookup_sound F9B002L44 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L60_lift _ (familyLookup_sound F9B002L60 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 28 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1064_closed
  · subst row; exact c8r1065_closed
  · subst row; exact c8r1066_closed
  · subst row; exact c8r1067_closed
  · subst row; exact c8r1068_closed
  · subst row; exact c8r1069_closed
  · subst row; exact c8r1070_closed
  · subst row; exact c8r1071_closed
theorem C8R01056G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1072_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r1072targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r1072choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1072targets [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)] c8r1072choice = true := by decide
    refine ⟨c8r1072targets, c8r1072choice, ?_, checked⟩
    intro S h
    simp only [c8r1072targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 2 _ (by rfl)))
  have c8r1073_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r1073targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r1073choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1073targets [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)] c8r1073choice = true := by decide
    refine ⟨c8r1073targets, c8r1073choice, ?_, checked⟩
    intro S h
    simp only [c8r1073targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 5 _ (by rfl)))
  have c8r1074_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r1074targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r1074choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1074targets [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)] c8r1074choice = true := by decide
    refine ⟨c8r1074targets, c8r1074choice, ?_, checked⟩
    intro S h
    simp only [c8r1074targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 7 _ (by rfl)))
  have c8r1075_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)] := by
    let c8r1075targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c8r1075choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1075targets [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)] c8r1075choice = true := by decide
    refine ⟨c8r1075targets, c8r1075choice, ?_, checked⟩
    intro S h
    simp only [c8r1075targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 9 _ (by rfl)))
  have c8r1076_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)] := by
    let c8r1076targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c8r1076choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1076targets [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)] c8r1076choice = true := by decide
    refine ⟨c8r1076targets, c8r1076choice, ?_, checked⟩
    intro S h
    simp only [c8r1076targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L45_lift _ (familyLookup_sound F9B001L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 12 _ (by rfl)))
  have c8r1077_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)] := by
    let c8r1077targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c8r1077choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1077targets [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)] c8r1077choice = true := by decide
    refine ⟨c8r1077targets, c8r1077choice, ?_, checked⟩
    intro S h
    simp only [c8r1077targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 14 _ (by rfl)))
  have c8r1078_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)] := by
    let c8r1078targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c8r1078choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1078targets [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)] c8r1078choice = true := by decide
    refine ⟨c8r1078targets, c8r1078choice, ?_, checked⟩
    intro S h
    simp only [c8r1078targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L52_lift _ (familyLookup_sound F9B001L52 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 17 _ (by rfl)))
  have c8r1079_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)] := by
    let c8r1079targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c8r1079choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1079targets [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)] c8r1079choice = true := by decide
    refine ⟨c8r1079targets, c8r1079choice, ?_, checked⟩
    intro S h
    simp only [c8r1079targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 20 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1072_closed
  · subst row; exact c8r1073_closed
  · subst row; exact c8r1074_closed
  · subst row; exact c8r1075_closed
  · subst row; exact c8r1076_closed
  · subst row; exact c8r1077_closed
  · subst row; exact c8r1078_closed
  · subst row; exact c8r1079_closed
theorem C8R01056G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1080_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)] := by
    let c8r1080targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,2)]]
    let c8r1080choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1080targets [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)] c8r1080choice = true := by decide
    refine ⟨c8r1080targets, c8r1080choice, ?_, checked⟩
    intro S h
    simp only [c8r1080targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 25 _ (by rfl)))
  have c8r1081_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)] := by
    let c8r1081targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(6,0)]]
    let c8r1081choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1081targets [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)] c8r1081choice = true := by decide
    refine ⟨c8r1081targets, c8r1081choice, ?_, checked⟩
    intro S h
    simp only [c8r1081targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 27 _ (by rfl)))
  have c8r1082_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)] := by
    let c8r1082targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(6,1)]]
    let c8r1082choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1082targets [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)] c8r1082choice = true := by decide
    refine ⟨c8r1082targets, c8r1082choice, ?_, checked⟩
    intro S h
    simp only [c8r1082targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L2_lift _ (familyLookup_sound F9B003L2 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 29 _ (by rfl)))
  have c8r1083_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)] := by
    let c8r1083targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,1)]]
    let c8r1083choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1083targets [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)] c8r1083choice = true := by decide
    refine ⟨c8r1083targets, c8r1083choice, ?_, checked⟩
    intro S h
    simp only [c8r1083targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 0 _ (by rfl)))
  have c8r1084_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)] := by
    let c8r1084targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(7,0)]]
    let c8r1084choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,-1),(13,(0,1))),((6,1),(14,(0,0))),((7,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1084targets [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)] c8r1084choice = true := by decide
    refine ⟨c8r1084targets, c8r1084choice, ?_, checked⟩
    intro S h
    simp only [c8r1084targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L3_lift _ (familyLookup_sound F9B003L3 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 2 _ (by rfl)))
  have c8r1085_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)] := by
    let c8r1085targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c8r1085choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,5),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1085targets [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)] c8r1085choice = true := by decide
    refine ⟨c8r1085targets, c8r1085choice, ?_, checked⟩
    intro S h
    simp only [c8r1085targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 7 _ (by rfl)))
  have c8r1086_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)] := by
    let c8r1086targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c8r1086choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1086targets [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)] c8r1086choice = true := by decide
    refine ⟨c8r1086targets, c8r1086choice, ?_, checked⟩
    intro S h
    simp only [c8r1086targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 11 _ (by rfl)))
  have c8r1087_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)] := by
    let c8r1087targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c8r1087choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1087targets [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)] c8r1087choice = true := by decide
    refine ⟨c8r1087targets, c8r1087choice, ?_, checked⟩
    intro S h
    simp only [c8r1087targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L53_lift _ (familyLookup_sound F9B001L53 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L52_lift _ (familyLookup_sound F9B000L52 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L61_lift _ (familyLookup_sound F9B002L61 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L48_lift _ (familyLookup_sound F9B001L48 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 13 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1080_closed
  · subst row; exact c8r1081_closed
  · subst row; exact c8r1082_closed
  · subst row; exact c8r1083_closed
  · subst row; exact c8r1084_closed
  · subst row; exact c8r1085_closed
  · subst row; exact c8r1086_closed
  · subst row; exact c8r1087_closed
theorem C8R01056_closed (row : List GridPoint) (h : FamilyMember row F8B000L33) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L33, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01056G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01056G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01056G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01056G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01056G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01056G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01056G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01056G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01056G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01056G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01056G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01056G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01056G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01056G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01056G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01056G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01056G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01056G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01056G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01056G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01056G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01056G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01056G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01056G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01056G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01056G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01056G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01056G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01056G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01056G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01056G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01056G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
