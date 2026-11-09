import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

theorem c8r96_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2)] := by
  let c8r96targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2)]]
  let c8r96choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r96targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2)] c8r96choice = true := by decide
  refine ⟨c8r96targets, c8r96choice, ?_, checked⟩
  intro S h
  simp only [c8r96targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 9 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 7 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L31_lift _ (familyLookup_sound F9B003L31 [] 31 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 5 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 19 _ (by rfl)))
theorem c8r97_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3)] := by
  let c8r97targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,3)]]
  let c8r97choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r97targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3)] c8r97choice = true := by decide
  refine ⟨c8r97targets, c8r97choice, ?_, checked⟩
  intro S h
  simp only [c8r97targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 10 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 8 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 0 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 6 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 21 _ (by rfl)))
theorem c8r98_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1)] := by
  let c8r98targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(3,1)]]
  let c8r98choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,2),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r98targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1)] c8r98choice = true := by decide
  refine ⟨c8r98targets, c8r98choice, ?_, checked⟩
  intro S h
  simp only [c8r98targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 11 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 9 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 1 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 11 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 13 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 24 _ (by rfl)))
theorem c8r99_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2)] := by
  let c8r99targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(3,2)]]
  let c8r99choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((3,0),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r99targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2)] c8r99choice = true := by decide
  refine ⟨c8r99targets, c8r99choice, ?_, checked⟩
  intro S h
  simp only [c8r99targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 12 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 10 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 2 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 12 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 14 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 27 _ (by rfl)))
theorem c8r100_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0)] := by
  let c8r100targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(4,0)]]
  let c8r100choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((3,-1),(12,(0,1))),((3,1),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r100targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0)] c8r100choice = true := by decide
  refine ⟨c8r100targets, c8r100choice, ?_, checked⟩
  intro S h
  simp only [c8r100targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 13 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 11 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 3 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 13 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 16 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 26 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 29 _ (by rfl)))
theorem c8r101_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2)] := by
  let c8r101targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(3,2)]]
  let c8r101choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r101targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2)] c8r101choice = true := by decide
  refine ⟨c8r101targets, c8r101choice, ?_, checked⟩
  intro S h
  simp only [c8r101targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 14 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 12 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 4 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 14 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 0 _ (by rfl)))
theorem c8r102_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3)] := by
  let c8r102targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(3,3)]]
  let c8r102choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r102targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3)] c8r102choice = true := by decide
  refine ⟨c8r102targets, c8r102choice, ?_, checked⟩
  intro S h
  simp only [c8r102targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 15 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 13 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 5 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 15 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 3 _ (by rfl)))
theorem c8r103_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2)] := by
  let c8r103targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2),(4,2)]]
  let c8r103choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((3,1),(12,(0,0))),((3,3),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r103targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2)] c8r103choice = true := by decide
  refine ⟨c8r103targets, c8r103choice, ?_, checked⟩
  intro S h
  simp only [c8r103targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 16 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 14 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 6 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 16 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 6 _ (by rfl)))
theorem c8r104_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5)] := by
  let c8r104targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,0),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,5)]]
  let c8r104choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,6),(10,(0,0))),((2,0),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r104targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5)] c8r104choice = true := by decide
  refine ⟨c8r104targets, c8r104choice, ?_, checked⟩
  intro S h
  simp only [c8r104targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 17 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 15 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 7 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 27 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 11 _ (by rfl)))
theorem c8r105_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0)] := by
  let c8r105targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(3,0)]]
  let c8r105choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,5),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((3,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r105targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0)] c8r105choice = true := by decide
  refine ⟨c8r105targets, c8r105choice, ?_, checked⟩
  intro S h
  simp only [c8r105targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 18 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 16 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 8 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 18 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 8 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 15 _ (by rfl)))
theorem c8r106_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3)] := by
  let c8r106targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,3)]]
  let c8r106choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r106targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3)] c8r106choice = true := by decide
  refine ⟨c8r106targets, c8r106choice, ?_, checked⟩
  intro S h
  simp only [c8r106targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 19 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 17 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 9 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 19 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 18 _ (by rfl)))
theorem c8r107_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4)] := by
  let c8r107targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(3,4)]]
  let c8r107choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r107targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4)] c8r107choice = true := by decide
  refine ⟨c8r107targets, c8r107choice, ?_, checked⟩
  intro S h
  simp only [c8r107targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 20 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 18 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 10 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L14_lift _ (familyLookup_sound F9B004L14 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 20 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 20 _ (by rfl)))
theorem c8r108_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1)] := by
  let c8r108targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(3,1)]]
  let c8r108choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((3,0),(13,(0,0))),((3,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r108targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1)] c8r108choice = true := by decide
  refine ⟨c8r108targets, c8r108choice, ?_, checked⟩
  intro S h
  simp only [c8r108targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 21 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 19 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 11 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 21 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 12 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 24 _ (by rfl)))
theorem c8r109_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3)] := by
  let c8r109targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(3,3)]]
  let c8r109choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,4),(13,(0,0))),((3,0),(14,(0,0))),((3,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r109targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3)] c8r109choice = true := by decide
  refine ⟨c8r109targets, c8r109choice, ?_, checked⟩
  intro S h
  simp only [c8r109targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 22 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 20 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 12 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 22 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 13 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 28 _ (by rfl)))
theorem c8r110_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0)] := by
  let c8r110targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0),(4,0)]]
  let c8r110choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((3,-1),(13,(0,1))),((3,1),(14,(0,0))),((4,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r110targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0)] c8r110choice = true := by decide
  refine ⟨c8r110targets, c8r110choice, ?_, checked⟩
  intro S h
  simp only [c8r110targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 23 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 21 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 13 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 23 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 15 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 27 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 30 _ (by rfl)))
theorem c8r111_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3)] := by
  let c8r111targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,3)]]
  let c8r111choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r111targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3)] c8r111choice = true := by decide
  refine ⟨c8r111targets, c8r111choice, ?_, checked⟩
  intro S h
  simp only [c8r111targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 24 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 22 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 14 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 24 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 2 _ (by rfl)))
theorem c8r112_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4)] := by
  let c8r112targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,4)]]
  let c8r112choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,5),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r112targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4)] c8r112choice = true := by decide
  refine ⟨c8r112targets, c8r112choice, ?_, checked⟩
  intro S h
  simp only [c8r112targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 25 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 23 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 15 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 25 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 5 _ (by rfl)))
theorem c8r113_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3)] := by
  let c8r113targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3)]]
  let c8r113choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,4),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r113targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3)] c8r113choice = true := by decide
  refine ⟨c8r113targets, c8r113choice, ?_, checked⟩
  intro S h
  simp only [c8r113targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 26 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 24 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 16 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 26 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 8 _ (by rfl)))
theorem c8r114_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2)] := by
  let c8r114targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,2)]]
  let c8r114choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,3),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r114targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2)] c8r114choice = true := by decide
  refine ⟨c8r114targets, c8r114choice, ?_, checked⟩
  intro S h
  simp only [c8r114targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 27 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 25 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 17 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 5 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 21 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 12 _ (by rfl)))
theorem c8r115_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0)] := by
  let c8r115targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(4,0)]]
  let c8r115choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((3,-1),(12,(0,1))),((3,1),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r115targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0)] c8r115choice = true := by decide
  refine ⟨c8r115targets, c8r115choice, ?_, checked⟩
  intro S h
  simp only [c8r115targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 28 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 26 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 18 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 6 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 23 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 10 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 14 _ (by rfl)))
theorem c8r116_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1)] := by
  let c8r116targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1),(4,1)]]
  let c8r116choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((3,0),(12,(0,0))),((3,2),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r116targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1)] c8r116choice = true := by decide
  refine ⟨c8r116targets, c8r116choice, ?_, checked⟩
  intro S h
  simp only [c8r116targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 29 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 27 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 19 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 7 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 24 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 16 _ (by rfl)))
theorem c8r117_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1)] := by
  let c8r117targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,1)]]
  let c8r117choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((3,-1),(12,(0,1))),((3,2),(13,(0,0))),((4,0),(14,(0,0))),((4,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r117targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1)] c8r117choice = true := by decide
  refine ⟨c8r117targets, c8r117choice, ?_, checked⟩
  intro S h
  simp only [c8r117targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 30 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 28 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 20 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 8 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 29 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 13 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 19 _ (by rfl)))
theorem c8r118_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0)] := by
  let c8r118targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0),(5,0)]]
  let c8r118choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((3,-1),(12,(0,1))),((3,1),(13,(0,0))),((4,-1),(14,(0,1))),((4,1),(15,(0,0))),((5,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r118targets [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0)] c8r118choice = true := by decide
  refine ⟨c8r118targets, c8r118choice, ?_, checked⟩
  intro S h
  simp only [c8r118targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 31 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 29 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 21 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 9 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 30 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 14 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 18 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 21 _ (by rfl)))
theorem c8r119_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4)] := by
  let c8r119targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)]]
  let c8r119choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r119targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4)] c8r119choice = true := by decide
  refine ⟨c8r119targets, c8r119choice, ?_, checked⟩
  intro S h
  simp only [c8r119targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 0 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 30 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 22 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 26 _ (by rfl)))
theorem c8r120_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1)] := by
  let c8r120targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)]]
  let c8r120choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r120targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1)] c8r120choice = true := by decide
  refine ⟨c8r120targets, c8r120choice, ?_, checked⟩
  intro S h
  simp only [c8r120targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 1 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L30_lift _ (familyLookup_sound F9B002L30 [] 31 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 23 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 30 _ (by rfl)))
theorem c8r121_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2)] := by
  let c8r121targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2)]]
  let c8r121choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r121targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2)] c8r121choice = true := by decide
  refine ⟨c8r121targets, c8r121choice, ?_, checked⟩
  intro S h
  simp only [c8r121targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 2 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 0 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 24 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 0 _ (by rfl)))
theorem c8r122_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3)] := by
  let c8r122targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3)]]
  let c8r122choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r122targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3)] c8r122choice = true := by decide
  refine ⟨c8r122targets, c8r122choice, ?_, checked⟩
  intro S h
  simp only [c8r122targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 3 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 1 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 25 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 2 _ (by rfl)))
theorem c8r123_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1)] := by
  let c8r123targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)]]
  let c8r123choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r123targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1)] c8r123choice = true := by decide
  refine ⟨c8r123targets, c8r123choice, ?_, checked⟩
  intro S h
  simp only [c8r123targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 4 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 2 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 26 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 27 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 5 _ (by rfl)))
theorem c8r124_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2)] := by
  let c8r124targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2)]]
  let c8r124choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r124targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2)] c8r124choice = true := by decide
  refine ⟨c8r124targets, c8r124choice, ?_, checked⟩
  intro S h
  simp only [c8r124targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 5 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 3 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 27 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 8 _ (by rfl)))
theorem c8r125_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1)] := by
  let c8r125targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,1)]]
  let c8r125choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r125targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1)] c8r125choice = true := by decide
  refine ⟨c8r125targets, c8r125choice, ?_, checked⟩
  intro S h
  simp only [c8r125targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 6 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 4 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 28 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 11 _ (by rfl)))
theorem c8r126_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3)] := by
  let c8r126targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,3)]]
  let c8r126choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r126targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3)] c8r126choice = true := by decide
  refine ⟨c8r126targets, c8r126choice, ?_, checked⟩
  intro S h
  simp only [c8r126targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 7 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 5 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 29 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 14 _ (by rfl)))
theorem c8r127_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2)] := by
  let c8r127targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2)]]
  let c8r127choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r127targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2)] c8r127choice = true := by decide
  refine ⟨c8r127targets, c8r127choice, ?_, checked⟩
  intro S h
  simp only [c8r127targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 8 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 6 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L32_lift _ (familyLookup_sound F9B003L32 [] 30 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L15_lift _ (familyLookup_sound F9B004L15 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 17 _ (by rfl)))
theorem C8R00096_closed (row : List GridPoint) (h : FamilyMember row F8B000L3) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L3, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c8r96_closed
  · subst row; exact c8r97_closed
  · subst row; exact c8r98_closed
  · subst row; exact c8r99_closed
  · subst row; exact c8r100_closed
  · subst row; exact c8r101_closed
  · subst row; exact c8r102_closed
  · subst row; exact c8r103_closed
  · subst row; exact c8r104_closed
  · subst row; exact c8r105_closed
  · subst row; exact c8r106_closed
  · subst row; exact c8r107_closed
  · subst row; exact c8r108_closed
  · subst row; exact c8r109_closed
  · subst row; exact c8r110_closed
  · subst row; exact c8r111_closed
  · subst row; exact c8r112_closed
  · subst row; exact c8r113_closed
  · subst row; exact c8r114_closed
  · subst row; exact c8r115_closed
  · subst row; exact c8r116_closed
  · subst row; exact c8r117_closed
  · subst row; exact c8r118_closed
  · subst row; exact c8r119_closed
  · subst row; exact c8r120_closed
  · subst row; exact c8r121_closed
  · subst row; exact c8r122_closed
  · subst row; exact c8r123_closed
  · subst row; exact c8r124_closed
  · subst row; exact c8r125_closed
  · subst row; exact c8r126_closed
  · subst row; exact c8r127_closed
end Polyomino57
