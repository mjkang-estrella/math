import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00288_closed (row : List GridPoint) (h : FamilyMember row F8B000L9) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r288_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2)] := by
    let c8r288targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)]]
    let c8r288choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r288targets [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2)] c8r288choice = true := by decide
    refine ⟨c8r288targets, c8r288choice, ?_, checked⟩
    intro S h
    simp only [c8r288targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L37_lift _ (familyLookup_sound F9B003L37 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 28 _ (by rfl)))
  have c8r289_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3)] := by
    let c8r289targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c8r289choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r289targets [(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3)] c8r289choice = true := by decide
    refine ⟨c8r289targets, c8r289choice, ?_, checked⟩
    intro S h
    simp only [c8r289targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 2 _ (by rfl)))
  have c8r290_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r290targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r290choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r290targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3)] c8r290choice = true := by decide
    refine ⟨c8r290targets, c8r290choice, ?_, checked⟩
    intro S h
    simp only [c8r290targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 8 _ (by rfl)))
  have c8r291_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r291targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r291choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r291targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0)] c8r291choice = true := by decide
    refine ⟨c8r291targets, c8r291choice, ?_, checked⟩
    intro S h
    simp only [c8r291targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 11 _ (by rfl)))
  have c8r292_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r292targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r292choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r292targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1)] c8r292choice = true := by decide
    refine ⟨c8r292targets, c8r292choice, ?_, checked⟩
    intro S h
    simp only [c8r292targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 13 _ (by rfl)))
  have c8r293_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r293targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r293choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r293targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2)] c8r293choice = true := by decide
    refine ⟨c8r293targets, c8r293choice, ?_, checked⟩
    intro S h
    simp only [c8r293targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 15 _ (by rfl)))
  have c8r294_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1)] := by
    let c8r294targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c8r294choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r294targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1)] c8r294choice = true := by decide
    refine ⟨c8r294targets, c8r294choice, ?_, checked⟩
    intro S h
    simp only [c8r294targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 18 _ (by rfl)))
  have c8r295_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0)] := by
    let c8r295targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c8r295choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r295targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0)] c8r295choice = true := by decide
    refine ⟨c8r295targets, c8r295choice, ?_, checked⟩
    intro S h
    simp only [c8r295targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 20 _ (by rfl)))
  have c8r296_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2)] := by
    let c8r296targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c8r296choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r296targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2)] c8r296choice = true := by decide
    refine ⟨c8r296targets, c8r296choice, ?_, checked⟩
    intro S h
    simp only [c8r296targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 23 _ (by rfl)))
  have c8r297_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1)] := by
    let c8r297targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c8r297choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r297targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1)] c8r297choice = true := by decide
    refine ⟨c8r297targets, c8r297choice, ?_, checked⟩
    intro S h
    simp only [c8r297targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 26 _ (by rfl)))
  have c8r298_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r298targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r298choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,5),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r298targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4)] c8r298choice = true := by decide
    refine ⟨c8r298targets, c8r298choice, ?_, checked⟩
    intro S h
    simp only [c8r298targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 31 _ (by rfl)))
  have c8r299_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r299targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r299choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r299targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1)] c8r299choice = true := by decide
    refine ⟨c8r299targets, c8r299choice, ?_, checked⟩
    intro S h
    simp only [c8r299targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 3 _ (by rfl)))
  have c8r300_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r300targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r300choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r300targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2)] c8r300choice = true := by decide
    refine ⟨c8r300targets, c8r300choice, ?_, checked⟩
    intro S h
    simp only [c8r300targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 5 _ (by rfl)))
  have c8r301_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r301targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r301choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r301targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3)] c8r301choice = true := by decide
    refine ⟨c8r301targets, c8r301choice, ?_, checked⟩
    intro S h
    simp only [c8r301targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 7 _ (by rfl)))
  have c8r302_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r302targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r302choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r302targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1)] c8r302choice = true := by decide
    refine ⟨c8r302targets, c8r302choice, ?_, checked⟩
    intro S h
    simp only [c8r302targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 10 _ (by rfl)))
  have c8r303_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2)] := by
    let c8r303targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c8r303choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r303targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2)] c8r303choice = true := by decide
    refine ⟨c8r303targets, c8r303choice, ?_, checked⟩
    intro S h
    simp only [c8r303targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 13 _ (by rfl)))
  have c8r304_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1)] := by
    let c8r304targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c8r304choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r304targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1)] c8r304choice = true := by decide
    refine ⟨c8r304targets, c8r304choice, ?_, checked⟩
    intro S h
    simp only [c8r304targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 16 _ (by rfl)))
  have c8r305_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3)] := by
    let c8r305targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c8r305choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r305targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3)] c8r305choice = true := by decide
    refine ⟨c8r305targets, c8r305choice, ?_, checked⟩
    intro S h
    simp only [c8r305targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 19 _ (by rfl)))
  have c8r306_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2)] := by
    let c8r306targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c8r306choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r306targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2)] c8r306choice = true := by decide
    refine ⟨c8r306targets, c8r306choice, ?_, checked⟩
    intro S h
    simp only [c8r306targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 22 _ (by rfl)))
  have c8r307_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2)] := by
    let c8r307targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c8r307choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r307targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2)] c8r307choice = true := by decide
    refine ⟨c8r307targets, c8r307choice, ?_, checked⟩
    intro S h
    simp only [c8r307targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 27 _ (by rfl)))
  have c8r308_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0)] := by
    let c8r308targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c8r308choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r308targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0)] c8r308choice = true := by decide
    refine ⟨c8r308targets, c8r308choice, ?_, checked⟩
    intro S h
    simp only [c8r308targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 29 _ (by rfl)))
  have c8r309_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1)] := by
    let c8r309targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c8r309choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r309targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1)] c8r309choice = true := by decide
    refine ⟨c8r309targets, c8r309choice, ?_, checked⟩
    intro S h
    simp only [c8r309targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 31 _ (by rfl)))
  have c8r310_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3)] := by
    let c8r310targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c8r310choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,4),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r310targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3)] c8r310choice = true := by decide
    refine ⟨c8r310targets, c8r310choice, ?_, checked⟩
    intro S h
    simp only [c8r310targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 3 _ (by rfl)))
  have c8r311_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1)] := by
    let c8r311targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c8r311choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r311targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1)] c8r311choice = true := by decide
    refine ⟨c8r311targets, c8r311choice, ?_, checked⟩
    intro S h
    simp only [c8r311targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 6 _ (by rfl)))
  have c8r312_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2)] := by
    let c8r312targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c8r312choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r312targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2)] c8r312choice = true := by decide
    refine ⟨c8r312targets, c8r312choice, ?_, checked⟩
    intro S h
    simp only [c8r312targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L36_lift _ (familyLookup_sound F9B002L36 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 8 _ (by rfl)))
  have c8r313_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1)] := by
    let c8r313targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c8r313choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r313targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1)] c8r313choice = true := by decide
    refine ⟨c8r313targets, c8r313choice, ?_, checked⟩
    intro S h
    simp only [c8r313targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 11 _ (by rfl)))
  have c8r314_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2)] := by
    let c8r314targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c8r314choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r314targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2)] c8r314choice = true := by decide
    refine ⟨c8r314targets, c8r314choice, ?_, checked⟩
    intro S h
    simp only [c8r314targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 14 _ (by rfl)))
  have c8r315_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1)] := by
    let c8r315targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c8r315choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,2),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r315targets [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1)] c8r315choice = true := by decide
    refine ⟨c8r315targets, c8r315choice, ?_, checked⟩
    intro S h
    simp only [c8r315targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 17 _ (by rfl)))
  have c8r316_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6)] := by
    let c8r316targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)]]
    let c8r316choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,7),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r316targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6)] c8r316choice = true := by decide
    refine ⟨c8r316targets, c8r316choice, ?_, checked⟩
    intro S h
    simp only [c8r316targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 23 _ (by rfl)))
  have c8r317_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2)] := by
    let c8r317targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)]]
    let c8r317choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,6),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0))),((3,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r317targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2)] c8r317choice = true := by decide
    refine ⟨c8r317targets, c8r317choice, ?_, checked⟩
    intro S h
    simp only [c8r317targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 28 _ (by rfl)))
  have c8r318_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3)] := by
    let c8r318targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)]]
    let c8r318choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,6),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((2,5),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r318targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3)] c8r318choice = true := by decide
    refine ⟨c8r318targets, c8r318choice, ?_, checked⟩
    intro S h
    simp only [c8r318targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 31 _ (by rfl)))
  have c8r319_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,4)] := by
    let c8r319targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)]]
    let c8r319choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,6),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r319targets [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,4)] c8r319choice = true := by decide
    refine ⟨c8r319targets, c8r319choice, ?_, checked⟩
    intro S h
    simp only [c8r319targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L38_lift _ (familyLookup_sound F9B003L38 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L33_lift _ (familyLookup_sound F9B000L33 [] 1 _ (by rfl)))
  simp only [F8B000L9, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c8r288_closed
  · subst row; exact c8r289_closed
  · subst row; exact c8r290_closed
  · subst row; exact c8r291_closed
  · subst row; exact c8r292_closed
  · subst row; exact c8r293_closed
  · subst row; exact c8r294_closed
  · subst row; exact c8r295_closed
  · subst row; exact c8r296_closed
  · subst row; exact c8r297_closed
  · subst row; exact c8r298_closed
  · subst row; exact c8r299_closed
  · subst row; exact c8r300_closed
  · subst row; exact c8r301_closed
  · subst row; exact c8r302_closed
  · subst row; exact c8r303_closed
  · subst row; exact c8r304_closed
  · subst row; exact c8r305_closed
  · subst row; exact c8r306_closed
  · subst row; exact c8r307_closed
  · subst row; exact c8r308_closed
  · subst row; exact c8r309_closed
  · subst row; exact c8r310_closed
  · subst row; exact c8r311_closed
  · subst row; exact c8r312_closed
  · subst row; exact c8r313_closed
  · subst row; exact c8r314_closed
  · subst row; exact c8r315_closed
  · subst row; exact c8r316_closed
  · subst row; exact c8r317_closed
  · subst row; exact c8r318_closed
  · subst row; exact c8r319_closed
end Polyomino57
