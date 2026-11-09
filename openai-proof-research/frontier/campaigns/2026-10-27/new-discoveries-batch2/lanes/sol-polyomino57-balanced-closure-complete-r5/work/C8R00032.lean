import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

theorem c8r32_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4)] := by
  let c8r32targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4)]]
  let c8r32choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,1),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r32targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4)] c8r32choice = true := by decide
  refine ⟨c8r32targets, c8r32choice, ?_, checked⟩
  intro S h
  simp only [c8r32targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 9 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 7 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 31 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 20 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 8 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 30 _ (by rfl)))
theorem c8r33_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0)] := by
  let c8r33targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0)]]
  let c8r33choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,-1),(11,(0,1))),((2,1),(12,(0,0))),((3,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r33targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0)] c8r33choice = true := by decide
  refine ⟨c8r33targets, c8r33choice, ?_, checked⟩
  intro S h
  simp only [c8r33targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 10 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 8 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 0 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 21 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 10 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 28 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 0 _ (by rfl)))
theorem c8r34_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1)] := by
  let c8r34targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1)]]
  let c8r34choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r34targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1)] c8r34choice = true := by decide
  refine ⟨c8r34targets, c8r34choice, ?_, checked⟩
  intro S h
  simp only [c8r34targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 11 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 9 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 1 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 22 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 11 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 2 _ (by rfl)))
theorem c8r35_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3)] := by
  let c8r35targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3)]]
  let c8r35choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r35targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3)] c8r35choice = true := by decide
  refine ⟨c8r35targets, c8r35choice, ?_, checked⟩
  intro S h
  simp only [c8r35targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 12 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 10 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 2 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 23 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 12 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 6 _ (by rfl)))
theorem c8r36_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4)] := by
  let c8r36targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,4)]]
  let c8r36choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r36targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4)] c8r36choice = true := by decide
  refine ⟨c8r36targets, c8r36choice, ?_, checked⟩
  intro S h
  simp only [c8r36targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 13 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 11 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 3 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 24 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 13 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 10 _ (by rfl)))
theorem c8r37_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0)] := by
  let c8r37targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(3,0)]]
  let c8r37choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,-1),(11,(0,1))),((2,1),(12,(0,0))),((2,2),(13,(0,0))),((3,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r37targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0)] c8r37choice = true := by decide
  refine ⟨c8r37targets, c8r37choice, ?_, checked⟩
  intro S h
  simp only [c8r37targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 14 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 12 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 4 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 25 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 15 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 8 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 13 _ (by rfl)))
theorem c8r38_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2)] := by
  let c8r38targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2),(3,2)]]
  let c8r38choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,1),(12,(0,0))),((2,3),(13,(0,0))),((3,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r38targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2)] c8r38choice = true := by decide
  refine ⟨c8r38targets, c8r38choice, ?_, checked⟩
  intro S h
  simp only [c8r38targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 15 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 13 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 5 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 26 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 16 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 16 _ (by rfl)))
theorem c8r39_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4)] := by
  let c8r39targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,4)]]
  let c8r39choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r39targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4)] c8r39choice = true := by decide
  refine ⟨c8r39targets, c8r39choice, ?_, checked⟩
  intro S h
  simp only [c8r39targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 16 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 14 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 6 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 27 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 17 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 20 _ (by rfl)))
theorem c8r40_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0)] := by
  let c8r40targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0)]]
  let c8r40choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,4),(10,(0,0))),((2,-1),(11,(0,1))),((2,1),(12,(0,0))),((2,3),(13,(0,0))),((3,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r40targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0)] c8r40choice = true := by decide
  refine ⟨c8r40targets, c8r40choice, ?_, checked⟩
  intro S h
  simp only [c8r40targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 17 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 15 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 7 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 28 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 19 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 18 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 23 _ (by rfl)))
theorem c8r41_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3)] := by
  let c8r41targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3)]]
  let c8r41choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((2,4),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r41targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3)] c8r41choice = true := by decide
  refine ⟨c8r41targets, c8r41choice, ?_, checked⟩
  intro S h
  simp only [c8r41targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 18 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 16 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 8 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 29 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 20 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 26 _ (by rfl)))
theorem c8r42_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5)] := by
  let c8r42targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5)]]
  let c8r42choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,6),(11,(0,0))),((2,0),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r42targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5)] c8r42choice = true := by decide
  refine ⟨c8r42targets, c8r42choice, ?_, checked⟩
  intro S h
  simp only [c8r42targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 19 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 17 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 9 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 30 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 21 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 30 _ (by rfl)))
theorem c8r43_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0)] := by
  let c8r43targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0)]]
  let c8r43choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,5),(11,(0,0))),((2,-1),(12,(0,1))),((2,1),(13,(0,0))),((2,4),(14,(0,0))),((3,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r43targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0)] c8r43choice = true := by decide
  refine ⟨c8r43targets, c8r43choice, ?_, checked⟩
  intro S h
  simp only [c8r43targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 20 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 18 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 10 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 31 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 22 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 28 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 1 _ (by rfl)))
theorem c8r44_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4)] := by
  let c8r44targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4)]]
  let c8r44choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,5),(11,(0,0))),((2,0),(12,(0,0))),((2,3),(13,(0,0))),((2,5),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r44targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4)] c8r44choice = true := by decide
  refine ⟨c8r44targets, c8r44choice, ?_, checked⟩
  intro S h
  simp only [c8r44targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 21 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 19 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 11 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 0 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 23 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 4 _ (by rfl)))
theorem c8r45_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1)] := by
  let c8r45targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1)]]
  let c8r45choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((2,-1),(12,(0,1))),((2,2),(13,(0,0))),((3,0),(14,(0,0))),((3,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r45targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1)] c8r45choice = true := by decide
  refine ⟨c8r45targets, c8r45choice, ?_, checked⟩
  intro S h
  simp only [c8r45targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 22 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 20 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 12 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 1 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 27 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 31 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 7 _ (by rfl)))
theorem c8r46_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0)] := by
  let c8r46targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0)]]
  let c8r46choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((2,-1),(12,(0,1))),((2,1),(13,(0,0))),((3,-1),(14,(0,1))),((3,1),(15,(0,0))),((4,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r46targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0)] c8r46choice = true := by decide
  refine ⟨c8r46targets, c8r46choice, ?_, checked⟩
  intro S h
  simp only [c8r46targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 23 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 21 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 13 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 2 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 28 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 1 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 6 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 9 _ (by rfl)))
theorem c8r47_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3)] := by
  let c8r47targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3)]]
  let c8r47choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r47targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3)] c8r47choice = true := by decide
  refine ⟨c8r47targets, c8r47choice, ?_, checked⟩
  intro S h
  simp only [c8r47targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 24 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 22 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 14 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 3 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 13 _ (by rfl)))
theorem c8r48_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4)] := by
  let c8r48targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,4)]]
  let c8r48choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,3),(8,(0,0))),((1,5),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r48targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4)] c8r48choice = true := by decide
  refine ⟨c8r48targets, c8r48choice, ?_, checked⟩
  intro S h
  simp only [c8r48targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 25 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 23 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 15 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 4 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 17 _ (by rfl)))
theorem c8r49_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1)] := by
  let c8r49targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,1)]]
  let c8r49choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r49targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1)] c8r49choice = true := by decide
  refine ⟨c8r49targets, c8r49choice, ?_, checked⟩
  intro S h
  simp only [c8r49targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 26 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 24 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 16 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 5 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 20 _ (by rfl)))
theorem c8r50_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2)] := by
  let c8r50targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,2)]]
  let c8r50choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r50targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2)] c8r50choice = true := by decide
  refine ⟨c8r50targets, c8r50choice, ?_, checked⟩
  intro S h
  simp only [c8r50targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 27 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 25 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 17 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 6 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 22 _ (by rfl)))
theorem c8r51_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4)] := by
  let c8r51targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,4)]]
  let c8r51choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,5),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r51targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4)] c8r51choice = true := by decide
  refine ⟨c8r51targets, c8r51choice, ?_, checked⟩
  intro S h
  simp only [c8r51targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 28 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 26 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 18 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 7 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 26 _ (by rfl)))
theorem c8r52_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1)] := by
  let c8r52targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(3,1)]]
  let c8r52choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r52targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1)] c8r52choice = true := by decide
  refine ⟨c8r52targets, c8r52choice, ?_, checked⟩
  intro S h
  simp only [c8r52targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 29 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 27 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 19 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 8 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 30 _ (by rfl)))
theorem c8r53_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3)] := by
  let c8r53targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(3,3)]]
  let c8r53choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r53targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3)] c8r53choice = true := by decide
  refine ⟨c8r53targets, c8r53choice, ?_, checked⟩
  intro S h
  simp only [c8r53targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 30 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 28 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 20 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 9 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 1 _ (by rfl)))
theorem c8r54_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5)] := by
  let c8r54targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,5)]]
  let c8r54choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,6),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r54targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5)] c8r54choice = true := by decide
  refine ⟨c8r54targets, c8r54choice, ?_, checked⟩
  intro S h
  simp only [c8r54targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 31 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 29 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 21 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 10 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 5 _ (by rfl)))
theorem c8r55_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1)] := by
  let c8r55targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,1)]]
  let c8r55choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((2,4),(13,(0,0))),((3,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r55targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1)] c8r55choice = true := by decide
  refine ⟨c8r55targets, c8r55choice, ?_, checked⟩
  intro S h
  simp only [c8r55targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 0 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 30 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 22 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 11 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 9 _ (by rfl)))
theorem c8r56_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4)] := by
  let c8r56targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(3,4)]]
  let c8r56choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r56targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4)] c8r56choice = true := by decide
  refine ⟨c8r56targets, c8r56choice, ?_, checked⟩
  intro S h
  simp only [c8r56targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 1 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 31 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 23 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 12 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 12 _ (by rfl)))
theorem c8r57_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1)] := by
  let c8r57targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)]]
  let c8r57choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,-1),(11,(0,1))),((2,2),(12,(0,0))),((3,0),(13,(0,0))),((3,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r57targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1)] c8r57choice = true := by decide
  refine ⟨c8r57targets, c8r57choice, ?_, checked⟩
  intro S h
  simp only [c8r57targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 2 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 0 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 24 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 13 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 6 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 15 _ (by rfl)))
theorem c8r58_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2)] := by
  let c8r58targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,2)]]
  let c8r58choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,3),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r58targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2)] c8r58choice = true := by decide
  refine ⟨c8r58targets, c8r58choice, ?_, checked⟩
  intro S h
  simp only [c8r58targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 3 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 1 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 25 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 14 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 18 _ (by rfl)))
theorem c8r59_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1)] := by
  let c8r59targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,1)]]
  let c8r59choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((3,0),(13,(0,0))),((3,2),(14,(0,0))),((4,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r59targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1)] c8r59choice = true := by decide
  refine ⟨c8r59targets, c8r59choice, ?_, checked⟩
  intro S h
  simp only [c8r59targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 4 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 2 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 26 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 15 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 21 _ (by rfl)))
theorem c8r60_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)] := by
  let c8r60targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4)]]
  let c8r60choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,5),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r60targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)] c8r60choice = true := by decide
  refine ⟨c8r60targets, c8r60choice, ?_, checked⟩
  intro S h
  simp only [c8r60targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 5 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 3 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 27 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 16 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 25 _ (by rfl)))
theorem c8r61_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2)] := by
  let c8r61targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,2)]]
  let c8r61choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r61targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2)] c8r61choice = true := by decide
  refine ⟨c8r61targets, c8r61choice, ?_, checked⟩
  intro S h
  simp only [c8r61targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 6 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 4 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 28 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 17 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 28 _ (by rfl)))
theorem c8r62_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3)] := by
  let c8r62targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3)]]
  let c8r62choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,4),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r62targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3)] c8r62choice = true := by decide
  refine ⟨c8r62targets, c8r62choice, ?_, checked⟩
  intro S h
  simp only [c8r62targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 7 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 5 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 29 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 18 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 30 _ (by rfl)))
theorem c8r63_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5)] := by
  let c8r63targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,5)]]
  let c8r63choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,6),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r63targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5)] c8r63choice = true := by decide
  refine ⟨c8r63targets, c8r63choice, ?_, checked⟩
  intro S h
  simp only [c8r63targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 8 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L29_lift _ (familyLookup_sound F9B002L29 [] 6 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L30_lift _ (familyLookup_sound F9B003L30 [] 30 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L13_lift _ (familyLookup_sound F9B004L13 [] 19 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L40_lift _ (familyLookup_sound F9B004L40 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 2 _ (by rfl)))
theorem C8R00032_closed (row : List GridPoint) (h : FamilyMember row F8B000L1) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L1, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c8r32_closed
  · subst row; exact c8r33_closed
  · subst row; exact c8r34_closed
  · subst row; exact c8r35_closed
  · subst row; exact c8r36_closed
  · subst row; exact c8r37_closed
  · subst row; exact c8r38_closed
  · subst row; exact c8r39_closed
  · subst row; exact c8r40_closed
  · subst row; exact c8r41_closed
  · subst row; exact c8r42_closed
  · subst row; exact c8r43_closed
  · subst row; exact c8r44_closed
  · subst row; exact c8r45_closed
  · subst row; exact c8r46_closed
  · subst row; exact c8r47_closed
  · subst row; exact c8r48_closed
  · subst row; exact c8r49_closed
  · subst row; exact c8r50_closed
  · subst row; exact c8r51_closed
  · subst row; exact c8r52_closed
  · subst row; exact c8r53_closed
  · subst row; exact c8r54_closed
  · subst row; exact c8r55_closed
  · subst row; exact c8r56_closed
  · subst row; exact c8r57_closed
  · subst row; exact c8r58_closed
  · subst row; exact c8r59_closed
  · subst row; exact c8r60_closed
  · subst row; exact c8r61_closed
  · subst row; exact c8r62_closed
  · subst row; exact c8r63_closed
end Polyomino57
