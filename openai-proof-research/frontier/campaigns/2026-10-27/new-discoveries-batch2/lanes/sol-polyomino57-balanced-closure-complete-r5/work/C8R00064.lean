import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

theorem c8r64_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2)] := by
  let c8r64targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,2)]]
  let c8r64choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((3,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r64targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2)] c8r64choice = true := by decide
  refine ⟨c8r64targets, c8r64choice, ?_, checked⟩
  intro S h
  simp only [c8r64targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 9 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 7 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 31 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 20 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 6 _ (by rfl)))
theorem c8r65_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4)] := by
  let c8r65targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(3,4)]]
  let c8r65choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r65targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4)] c8r65choice = true := by decide
  refine ⟨c8r65targets, c8r65choice, ?_, checked⟩
  intro S h
  simp only [c8r65targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 10 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 8 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 0 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 21 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 9 _ (by rfl)))
theorem c8r66_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2)] := by
  let c8r66targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2)]]
  let c8r66choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,3),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r66targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2)] c8r66choice = true := by decide
  refine ⟨c8r66targets, c8r66choice, ?_, checked⟩
  intro S h
  simp only [c8r66targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 11 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 9 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 1 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 22 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 13 _ (by rfl)))
theorem c8r67_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3)] := by
  let c8r67targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,3)]]
  let c8r67choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r67targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3)] c8r67choice = true := by decide
  refine ⟨c8r67targets, c8r67choice, ?_, checked⟩
  intro S h
  simp only [c8r67targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 12 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 10 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 2 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 23 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 16 _ (by rfl)))
theorem c8r68_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2)] := by
  let c8r68targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,2)]]
  let c8r68choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((3,1),(13,(0,0))),((3,3),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r68targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2)] c8r68choice = true := by decide
  refine ⟨c8r68targets, c8r68choice, ?_, checked⟩
  intro S h
  simp only [c8r68targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 13 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 11 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 3 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 24 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 19 _ (by rfl)))
theorem c8r69_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5)] := by
  let c8r69targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5)]]
  let c8r69choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,6),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r69targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5)] c8r69choice = true := by decide
  refine ⟨c8r69targets, c8r69choice, ?_, checked⟩
  intro S h
  simp only [c8r69targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 14 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 12 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 4 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 25 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 23 _ (by rfl)))
theorem c8r70_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3)] := by
  let c8r70targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3)]]
  let c8r70choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,5),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r70targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3)] c8r70choice = true := by decide
  refine ⟨c8r70targets, c8r70choice, ?_, checked⟩
  intro S h
  simp only [c8r70targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 15 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 13 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 5 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 26 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 26 _ (by rfl)))
theorem c8r71_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)] := by
  let c8r71targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4)]]
  let c8r71choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,5),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r71targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)] c8r71choice = true := by decide
  refine ⟨c8r71targets, c8r71choice, ?_, checked⟩
  intro S h
  simp only [c8r71targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 16 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 14 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 6 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 27 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 28 _ (by rfl)))
theorem c8r72_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3)] := by
  let c8r72targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,3)]]
  let c8r72choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,4),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r72targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3)] c8r72choice = true := by decide
  refine ⟨c8r72targets, c8r72choice, ?_, checked⟩
  intro S h
  simp only [c8r72targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 17 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 15 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 7 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 28 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 0 _ (by rfl)))
theorem c8r73_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4)] := by
  let c8r73targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4),(3,4)]]
  let c8r73choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,4),(10,(0,0))),((2,2),(11,(0,0))),((2,5),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r73targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4)] c8r73choice = true := by decide
  refine ⟨c8r73targets, c8r73choice, ?_, checked⟩
  intro S h
  simp only [c8r73targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 18 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 16 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 8 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 29 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 3 _ (by rfl)))
theorem c8r74_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3)] := by
  let c8r74targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,3)]]
  let c8r74choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,4),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,4),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r74targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3)] c8r74choice = true := by decide
  refine ⟨c8r74targets, c8r74choice, ?_, checked⟩
  intro S h
  simp only [c8r74targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 19 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 17 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 9 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 30 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 6 _ (by rfl)))
theorem c8r75_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6)] := by
  let c8r75targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,6)]]
  let c8r75choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,7),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r75targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6)] c8r75choice = true := by decide
  refine ⟨c8r75targets, c8r75choice, ?_, checked⟩
  intro S h
  simp only [c8r75targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 20 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 18 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 10 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 31 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 10 _ (by rfl)))
theorem c8r76_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4)] := by
  let c8r76targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,4)]]
  let c8r76choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,6),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r76targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4)] c8r76choice = true := by decide
  refine ⟨c8r76targets, c8r76choice, ?_, checked⟩
  intro S h
  simp only [c8r76targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 21 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 19 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 11 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 0 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 13 _ (by rfl)))
theorem c8r77_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5)] := by
  let c8r77targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(3,5)]]
  let c8r77choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,6),(11,(0,0))),((2,4),(12,(0,0))),((2,6),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r77targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5)] c8r77choice = true := by decide
  refine ⟨c8r77targets, c8r77choice, ?_, checked⟩
  intro S h
  simp only [c8r77targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 22 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 20 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 12 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 1 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 15 _ (by rfl)))
theorem c8r78_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,3),(2,4)] := by
  let c8r78targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,3),(2,4),(3,4)]]
  let c8r78choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,5),(11,(0,0))),((2,2),(12,(0,0))),((2,5),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r78targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,3),(2,4)] c8r78choice = true := by decide
  refine ⟨c8r78targets, c8r78choice, ?_, checked⟩
  intro S h
  simp only [c8r78targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 23 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 21 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 13 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 2 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 19 _ (by rfl)))
theorem c8r79_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(2,5)] := by
  let c8r79targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(2,5),(3,5)]]
  let c8r79choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,5),(11,(0,0))),((2,3),(12,(0,0))),((2,6),(13,(0,0))),((3,4),(14,(0,0))),((3,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r79targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(2,5)] c8r79choice = true := by decide
  refine ⟨c8r79targets, c8r79choice, ?_, checked⟩
  intro S h
  simp only [c8r79targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 24 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 22 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 14 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 3 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 22 _ (by rfl)))
theorem c8r80_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4)] := by
  let c8r80targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(4,4)]]
  let c8r80choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,5),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,3),(14,(0,0))),((3,5),(15,(0,0))),((4,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r80targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4)] c8r80choice = true := by decide
  refine ⟨c8r80targets, c8r80choice, ?_, checked⟩
  intro S h
  simp only [c8r80targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 25 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 23 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 15 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 4 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 25 _ (by rfl)))
theorem c8r81_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5)] := by
  let c8r81targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(0,6),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,0),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,5)]]
  let c8r81choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,5),(4,(1,0))),((0,-1),(5,(0,1))),((0,4),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,6),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r81targets [(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5)] c8r81choice = true := by decide
  refine ⟨c8r81targets, c8r81choice, ?_, checked⟩
  intro S h
  simp only [c8r81targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 26 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 24 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 16 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 5 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 1 _ (by rfl)))
theorem c8r82_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)] := by
  let c8r82targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)]]
  let c8r82choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r82targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)] c8r82choice = true := by decide
  refine ⟨c8r82targets, c8r82choice, ?_, checked⟩
  intro S h
  simp only [c8r82targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 27 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 25 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 17 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 18 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 7 _ (by rfl)))
theorem c8r83_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)] := by
  let c8r83targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)]]
  let c8r83choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((3,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r83targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)] c8r83choice = true := by decide
  refine ⟨c8r83targets, c8r83choice, ?_, checked⟩
  intro S h
  simp only [c8r83targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 28 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 26 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 18 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 20 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 4 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 10 _ (by rfl)))
theorem c8r84_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)] := by
  let c8r84targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)]]
  let c8r84choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r84targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)] c8r84choice = true := by decide
  refine ⟨c8r84targets, c8r84choice, ?_, checked⟩
  intro S h
  simp only [c8r84targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 29 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 27 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 19 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 21 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 12 _ (by rfl)))
theorem c8r85_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)] := by
  let c8r85targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)]]
  let c8r85choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r85targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)] c8r85choice = true := by decide
  refine ⟨c8r85targets, c8r85choice, ?_, checked⟩
  intro S h
  simp only [c8r85targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 30 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 28 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 20 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 22 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 14 _ (by rfl)))
theorem c8r86_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4)] := by
  let c8r86targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4)]]
  let c8r86choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r86targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4)] c8r86choice = true := by decide
  refine ⟨c8r86targets, c8r86choice, ?_, checked⟩
  intro S h
  simp only [c8r86targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 31 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 29 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 21 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 23 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 19 _ (by rfl)))
theorem c8r87_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0)] := by
  let c8r87targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0)]]
  let c8r87choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r87targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0)] c8r87choice = true := by decide
  refine ⟨c8r87targets, c8r87choice, ?_, checked⟩
  intro S h
  simp only [c8r87targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 0 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 30 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 22 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 24 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 16 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 22 _ (by rfl)))
theorem c8r88_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1)] := by
  let c8r88targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1)]]
  let c8r88choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r88targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1)] c8r88choice = true := by decide
  refine ⟨c8r88targets, c8r88choice, ?_, checked⟩
  intro S h
  simp only [c8r88targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 1 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 31 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 23 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 25 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 25 _ (by rfl)))
theorem c8r89_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3)] := by
  let c8r89targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3)]]
  let c8r89choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r89targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3)] c8r89choice = true := by decide
  refine ⟨c8r89targets, c8r89choice, ?_, checked⟩
  intro S h
  simp only [c8r89targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 2 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 0 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 24 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 26 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 28 _ (by rfl)))
theorem c8r90_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1)] := by
  let c8r90targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)]]
  let c8r90choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,2),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r90targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1)] c8r90choice = true := by decide
  refine ⟨c8r90targets, c8r90choice, ?_, checked⟩
  intro S h
  simp only [c8r90targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 3 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 1 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 25 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 31 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 20 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 31 _ (by rfl)))
theorem c8r91_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0)] := by
  let c8r91targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0)]]
  let c8r91choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r91targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0)] c8r91choice = true := by decide
  refine ⟨c8r91targets, c8r91choice, ?_, checked⟩
  intro S h
  simp only [c8r91targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 4 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 2 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 26 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 0 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 22 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 30 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 1 _ (by rfl)))
theorem c8r92_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2)] := by
  let c8r92targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2)]]
  let c8r92choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r92targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2)] c8r92choice = true := by decide
  refine ⟨c8r92targets, c8r92choice, ?_, checked⟩
  intro S h
  simp only [c8r92targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 5 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 3 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 27 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 1 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 4 _ (by rfl)))
theorem c8r93_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1)] := by
  let c8r93targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1)]]
  let c8r93choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r93targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1)] c8r93choice = true := by decide
  refine ⟨c8r93targets, c8r93choice, ?_, checked⟩
  intro S h
  simp only [c8r93targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 6 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 4 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 28 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 2 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 7 _ (by rfl)))
theorem c8r94_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4)] := by
  let c8r94targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4)]]
  let c8r94choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r94targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4)] c8r94choice = true := by decide
  refine ⟨c8r94targets, c8r94choice, ?_, checked⟩
  intro S h
  simp only [c8r94targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 7 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 5 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 29 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 3 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 12 _ (by rfl)))
theorem c8r95_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0)] := by
  let c8r95targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0)]]
  let c8r95choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((3,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r95targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0)] c8r95choice = true := by decide
  refine ⟨c8r95targets, c8r95choice, ?_, checked⟩
  intro S h
  simp only [c8r95targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 8 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 6 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 30 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 4 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 9 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 16 _ (by rfl)))
theorem C8R00064_closed (row : List GridPoint) (h : FamilyMember row F8B000L2) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L2, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c8r64_closed
  · subst row; exact c8r65_closed
  · subst row; exact c8r66_closed
  · subst row; exact c8r67_closed
  · subst row; exact c8r68_closed
  · subst row; exact c8r69_closed
  · subst row; exact c8r70_closed
  · subst row; exact c8r71_closed
  · subst row; exact c8r72_closed
  · subst row; exact c8r73_closed
  · subst row; exact c8r74_closed
  · subst row; exact c8r75_closed
  · subst row; exact c8r76_closed
  · subst row; exact c8r77_closed
  · subst row; exact c8r78_closed
  · subst row; exact c8r79_closed
  · subst row; exact c8r80_closed
  · subst row; exact c8r81_closed
  · subst row; exact c8r82_closed
  · subst row; exact c8r83_closed
  · subst row; exact c8r84_closed
  · subst row; exact c8r85_closed
  · subst row; exact c8r86_closed
  · subst row; exact c8r87_closed
  · subst row; exact c8r88_closed
  · subst row; exact c8r89_closed
  · subst row; exact c8r90_closed
  · subst row; exact c8r91_closed
  · subst row; exact c8r92_closed
  · subst row; exact c8r93_closed
  · subst row; exact c8r94_closed
  · subst row; exact c8r95_closed
end Polyomino57
