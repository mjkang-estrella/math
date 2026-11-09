import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

theorem c8r128_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5)] := by
  let c8r128targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5)]]
  let c8r128choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,6),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r128targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5)] c8r128choice = true := by decide
  refine ⟨c8r128targets, c8r128choice, ?_, checked⟩
  intro S h
  simp only [c8r128targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 9 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 7 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 31 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 22 _ (by rfl)))
theorem c8r129_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1)] := by
  let c8r129targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(3,1)]]
  let c8r129choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r129targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1)] c8r129choice = true := by decide
  refine ⟨c8r129targets, c8r129choice, ?_, checked⟩
  intro S h
  simp only [c8r129targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 10 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 8 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 0 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 27 _ (by rfl)))
theorem c8r130_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3)] := by
  let c8r130targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3)]]
  let c8r130choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r130targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3)] c8r130choice = true := by decide
  refine ⟨c8r130targets, c8r130choice, ?_, checked⟩
  intro S h
  simp only [c8r130targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 11 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 9 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 1 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 30 _ (by rfl)))
theorem c8r131_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4)] := by
  let c8r131targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4)]]
  let c8r131choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r131targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4)] c8r131choice = true := by decide
  refine ⟨c8r131targets, c8r131choice, ?_, checked⟩
  intro S h
  simp only [c8r131targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 12 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 10 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 2 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 0 _ (by rfl)))
theorem c8r132_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1)] := by
  let c8r132targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1)]]
  let c8r132choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r132targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1)] c8r132choice = true := by decide
  refine ⟨c8r132targets, c8r132choice, ?_, checked⟩
  intro S h
  simp only [c8r132targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 13 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 11 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 3 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 23 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 4 _ (by rfl)))
theorem c8r133_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2)] := by
  let c8r133targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,2)]]
  let c8r133choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r133targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2)] c8r133choice = true := by decide
  refine ⟨c8r133targets, c8r133choice, ?_, checked⟩
  intro S h
  simp only [c8r133targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 14 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 12 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 4 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 7 _ (by rfl)))
theorem c8r134_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3)] := by
  let c8r134targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3),(3,3)]]
  let c8r134choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r134targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3)] c8r134choice = true := by decide
  refine ⟨c8r134targets, c8r134choice, ?_, checked⟩
  intro S h
  simp only [c8r134targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 15 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 13 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 5 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 10 _ (by rfl)))
theorem c8r135_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1)] := by
  let c8r135targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,1)]]
  let c8r135choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,0),(12,(0,0))),((3,2),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r135targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1)] c8r135choice = true := by decide
  refine ⟨c8r135targets, c8r135choice, ?_, checked⟩
  intro S h
  simp only [c8r135targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 16 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 14 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 6 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 13 _ (by rfl)))
theorem c8r136_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3)] := by
  let c8r136targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,3)]]
  let c8r136choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r136targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3)] c8r136choice = true := by decide
  refine ⟨c8r136targets, c8r136choice, ?_, checked⟩
  intro S h
  simp only [c8r136targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 17 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 15 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 7 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 16 _ (by rfl)))
theorem c8r137_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4)] := by
  let c8r137targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(3,4)]]
  let c8r137choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,5),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r137targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4)] c8r137choice = true := by decide
  refine ⟨c8r137targets, c8r137choice, ?_, checked⟩
  intro S h
  simp only [c8r137targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 18 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 16 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 8 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 19 _ (by rfl)))
theorem c8r138_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3)] := by
  let c8r138targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,3)]]
  let c8r138choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r138targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3)] c8r138choice = true := by decide
  refine ⟨c8r138targets, c8r138choice, ?_, checked⟩
  intro S h
  simp only [c8r138targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 19 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 17 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 9 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 22 _ (by rfl)))
theorem c8r139_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2)] := by
  let c8r139targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2)]]
  let c8r139choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r139targets [(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2)] c8r139choice = true := by decide
  refine ⟨c8r139targets, c8r139choice, ?_, checked⟩
  intro S h
  simp only [c8r139targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 20 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 18 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 10 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 1 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 26 _ (by rfl)))
theorem c8r140_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0)] := by
  let c8r140targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0)]]
  let c8r140choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,2),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r140targets [(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0)] c8r140choice = true := by decide
  refine ⟨c8r140targets, c8r140choice, ?_, checked⟩
  intro S h
  simp only [c8r140targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 21 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 19 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 11 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 3 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 24 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 28 _ (by rfl)))
theorem c8r141_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1)] := by
  let c8r141targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1)]]
  let c8r141choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,2),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r141targets [(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1)] c8r141choice = true := by decide
  refine ⟨c8r141targets, c8r141choice, ?_, checked⟩
  intro S h
  simp only [c8r141targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 22 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 20 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 12 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 4 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 30 _ (by rfl)))
theorem c8r142_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3)] := by
  let c8r142targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,3)]]
  let c8r142choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r142targets [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3)] c8r142choice = true := by decide
  refine ⟨c8r142targets, c8r142choice, ?_, checked⟩
  intro S h
  simp only [c8r142targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 23 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 21 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 13 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 2 _ (by rfl)))
theorem c8r143_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1)] := by
  let c8r143targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,1)]]
  let c8r143choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r143targets [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1)] c8r143choice = true := by decide
  refine ⟨c8r143targets, c8r143choice, ?_, checked⟩
  intro S h
  simp only [c8r143targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 24 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 22 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 14 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 5 _ (by rfl)))
theorem c8r144_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2)] := by
  let c8r144targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2),(4,2)]]
  let c8r144choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r144targets [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2)] c8r144choice = true := by decide
  refine ⟨c8r144targets, c8r144choice, ?_, checked⟩
  intro S h
  simp only [c8r144targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 25 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 23 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 15 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 7 _ (by rfl)))
theorem c8r145_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1)] := by
  let c8r145targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1)]]
  let c8r145choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((3,-1),(11,(0,1))),((3,2),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r145targets [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1)] c8r145choice = true := by decide
  refine ⟨c8r145targets, c8r145choice, ?_, checked⟩
  intro S h
  simp only [c8r145targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 26 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 24 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 16 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 3 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 10 _ (by rfl)))
theorem c8r146_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2)] := by
  let c8r146targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,2)]]
  let c8r146choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r146targets [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2)] c8r146choice = true := by decide
  refine ⟨c8r146targets, c8r146choice, ?_, checked⟩
  intro S h
  simp only [c8r146targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 27 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 25 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 17 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 13 _ (by rfl)))
theorem c8r147_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1)] := by
  let c8r147targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(5,1)]]
  let c8r147choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,0),(13,(0,0))),((4,2),(14,(0,0))),((5,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r147targets [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1)] c8r147choice = true := by decide
  refine ⟨c8r147targets, c8r147choice, ?_, checked⟩
  intro S h
  simp only [c8r147targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 28 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 26 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 18 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 16 _ (by rfl)))
theorem c8r148_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5)] := by
  let c8r148targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5)]]
  let c8r148choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,6),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r148targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5)] c8r148choice = true := by decide
  refine ⟨c8r148targets, c8r148choice, ?_, checked⟩
  intro S h
  simp only [c8r148targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 29 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 27 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 19 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 21 _ (by rfl)))
theorem c8r149_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2)] := by
  let c8r149targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2)]]
  let c8r149choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r149targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2)] c8r149choice = true := by decide
  refine ⟨c8r149targets, c8r149choice, ?_, checked⟩
  intro S h
  simp only [c8r149targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 30 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 28 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 20 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 25 _ (by rfl)))
theorem c8r150_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3)] := by
  let c8r150targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3)]]
  let c8r150choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r150targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3)] c8r150choice = true := by decide
  refine ⟨c8r150targets, c8r150choice, ?_, checked⟩
  intro S h
  simp only [c8r150targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 31 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 29 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 21 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 27 _ (by rfl)))
theorem c8r151_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4)] := by
  let c8r151targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4)]]
  let c8r151choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r151targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4)] c8r151choice = true := by decide
  refine ⟨c8r151targets, c8r151choice, ?_, checked⟩
  intro S h
  simp only [c8r151targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 0 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 30 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 22 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 29 _ (by rfl)))
theorem c8r152_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2)] := by
  let c8r152targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,2)]]
  let c8r152choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r152targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2)] c8r152choice = true := by decide
  refine ⟨c8r152targets, c8r152choice, ?_, checked⟩
  intro S h
  simp only [c8r152targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 1 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 31 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 23 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 1 _ (by rfl)))
theorem c8r153_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3)] := by
  let c8r153targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,3)]]
  let c8r153choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r153targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3)] c8r153choice = true := by decide
  refine ⟨c8r153targets, c8r153choice, ?_, checked⟩
  intro S h
  simp only [c8r153targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 2 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 0 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 24 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 4 _ (by rfl)))
theorem c8r154_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2)] := by
  let c8r154targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,2)]]
  let c8r154choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r154targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2)] c8r154choice = true := by decide
  refine ⟨c8r154targets, c8r154choice, ?_, checked⟩
  intro S h
  simp only [c8r154targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 3 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 1 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 25 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 7 _ (by rfl)))
theorem c8r155_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4)] := by
  let c8r155targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(3,4)]]
  let c8r155choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,4),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r155targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4)] c8r155choice = true := by decide
  refine ⟨c8r155targets, c8r155choice, ?_, checked⟩
  intro S h
  simp only [c8r155targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 4 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 2 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 26 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 10 _ (by rfl)))
theorem c8r156_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3)] := by
  let c8r156targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,3)]]
  let c8r156choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,4),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r156targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3)] c8r156choice = true := by decide
  refine ⟨c8r156targets, c8r156choice, ?_, checked⟩
  intro S h
  simp only [c8r156targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 5 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 3 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 27 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 13 _ (by rfl)))
theorem c8r157_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2)] := by
  let c8r157targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)]]
  let c8r157choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r157targets [(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2)] c8r157choice = true := by decide
  refine ⟨c8r157targets, c8r157choice, ?_, checked⟩
  intro S h
  simp only [c8r157targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 6 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 4 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 28 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 30 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 18 _ (by rfl)))
theorem c8r158_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3)] := by
  let c8r158targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,3)]]
  let c8r158choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r158targets [(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3)] c8r158choice = true := by decide
  refine ⟨c8r158targets, c8r158choice, ?_, checked⟩
  intro S h
  simp only [c8r158targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 7 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 5 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 29 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 22 _ (by rfl)))
theorem c8r159_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1)] := by
  let c8r159targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1)]]
  let c8r159choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r159targets [(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1)] c8r159choice = true := by decide
  refine ⟨c8r159targets, c8r159choice, ?_, checked⟩
  intro S h
  simp only [c8r159targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 8 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 6 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 30 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 25 _ (by rfl)))
theorem C8R00128_closed (row : List GridPoint) (h : FamilyMember row F8B000L4) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L4, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c8r128_closed
  · subst row; exact c8r129_closed
  · subst row; exact c8r130_closed
  · subst row; exact c8r131_closed
  · subst row; exact c8r132_closed
  · subst row; exact c8r133_closed
  · subst row; exact c8r134_closed
  · subst row; exact c8r135_closed
  · subst row; exact c8r136_closed
  · subst row; exact c8r137_closed
  · subst row; exact c8r138_closed
  · subst row; exact c8r139_closed
  · subst row; exact c8r140_closed
  · subst row; exact c8r141_closed
  · subst row; exact c8r142_closed
  · subst row; exact c8r143_closed
  · subst row; exact c8r144_closed
  · subst row; exact c8r145_closed
  · subst row; exact c8r146_closed
  · subst row; exact c8r147_closed
  · subst row; exact c8r148_closed
  · subst row; exact c8r149_closed
  · subst row; exact c8r150_closed
  · subst row; exact c8r151_closed
  · subst row; exact c8r152_closed
  · subst row; exact c8r153_closed
  · subst row; exact c8r154_closed
  · subst row; exact c8r155_closed
  · subst row; exact c8r156_closed
  · subst row; exact c8r157_closed
  · subst row; exact c8r158_closed
  · subst row; exact c8r159_closed
end Polyomino57
