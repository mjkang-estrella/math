import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01248G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1248_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1248targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1248choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1248targets [(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3)] c8r1248choice = true := by decide
    refine ⟨c8r1248targets, c8r1248choice, ?_, checked⟩
    intro S h
    simp only [c8r1248targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 2 _ (by rfl)))
  have c8r1249_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r1249targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r1249choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1249targets [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)] c8r1249choice = true := by decide
    refine ⟨c8r1249targets, c8r1249choice, ?_, checked⟩
    intro S h
    simp only [c8r1249targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 30 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L43_lift _ (familyLookup_sound F9B004L43 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 12 _ (by rfl)))
  have c8r1250_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r1250targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r1250choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,6),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1250targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r1250choice = true := by decide
    refine ⟨c8r1250targets, c8r1250choice, ?_, checked⟩
    intro S h
    simp only [c8r1250targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 22 _ (by rfl)))
  have c8r1251_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] := by
    let c8r1251targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
    let c8r1251choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1251targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] c8r1251choice = true := by decide
    refine ⟨c8r1251targets, c8r1251choice, ?_, checked⟩
    intro S h
    simp only [c8r1251targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L18_lift _ (familyLookup_sound F9B003L18 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 27 _ (by rfl)))
  have c8r1252_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c8r1252targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c8r1252choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1252targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] c8r1252choice = true := by decide
    refine ⟨c8r1252targets, c8r1252choice, ?_, checked⟩
    intro S h
    simp only [c8r1252targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 31 _ (by rfl)))
  have c8r1253_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c8r1253targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c8r1253choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1253targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] c8r1253choice = true := by decide
    refine ⟨c8r1253targets, c8r1253choice, ?_, checked⟩
    intro S h
    simp only [c8r1253targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 2 _ (by rfl)))
  have c8r1254_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c8r1254targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c8r1254choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1254targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] c8r1254choice = true := by decide
    refine ⟨c8r1254targets, c8r1254choice, ?_, checked⟩
    intro S h
    simp only [c8r1254targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 4 _ (by rfl)))
  have c8r1255_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r1255targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r1255choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1255targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] c8r1255choice = true := by decide
    refine ⟨c8r1255targets, c8r1255choice, ?_, checked⟩
    intro S h
    simp only [c8r1255targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 6 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1248_closed
  · subst row; exact c8r1249_closed
  · subst row; exact c8r1250_closed
  · subst row; exact c8r1251_closed
  · subst row; exact c8r1252_closed
  · subst row; exact c8r1253_closed
  · subst row; exact c8r1254_closed
  · subst row; exact c8r1255_closed
theorem C8R01248G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1256_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c8r1256targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c8r1256choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1256targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] c8r1256choice = true := by decide
    refine ⟨c8r1256targets, c8r1256choice, ?_, checked⟩
    intro S h
    simp only [c8r1256targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L18_lift _ (familyLookup_sound F9B003L18 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 10 _ (by rfl)))
  have c8r1257_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] := by
    let c8r1257targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)]]
    let c8r1257choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1257targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] c8r1257choice = true := by decide
    refine ⟨c8r1257targets, c8r1257choice, ?_, checked⟩
    intro S h
    simp only [c8r1257targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L18_lift _ (familyLookup_sound F9B003L18 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 13 _ (by rfl)))
  have c8r1258_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] := by
    let c8r1258targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)]]
    let c8r1258choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1258targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] c8r1258choice = true := by decide
    refine ⟨c8r1258targets, c8r1258choice, ?_, checked⟩
    intro S h
    simp only [c8r1258targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L18_lift _ (familyLookup_sound F9B003L18 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 16 _ (by rfl)))
  have c8r1259_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] := by
    let c8r1259targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)]]
    let c8r1259choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1259targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] c8r1259choice = true := by decide
    refine ⟨c8r1259targets, c8r1259choice, ?_, checked⟩
    intro S h
    simp only [c8r1259targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 18 _ (by rfl)))
  have c8r1260_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] := by
    let c8r1260targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
    let c8r1260choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1260targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] c8r1260choice = true := by decide
    refine ⟨c8r1260targets, c8r1260choice, ?_, checked⟩
    intro S h
    simp only [c8r1260targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 21 _ (by rfl)))
  have c8r1261_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] := by
    let c8r1261targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
    let c8r1261choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1261targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] c8r1261choice = true := by decide
    refine ⟨c8r1261targets, c8r1261choice, ?_, checked⟩
    intro S h
    simp only [c8r1261targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 24 _ (by rfl)))
  have c8r1262_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] := by
    let c8r1262targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
    let c8r1262choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1262targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] c8r1262choice = true := by decide
    refine ⟨c8r1262targets, c8r1262choice, ?_, checked⟩
    intro S h
    simp only [c8r1262targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 27 _ (by rfl)))
  have c8r1263_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] := by
    let c8r1263targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
    let c8r1263choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1263targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] c8r1263choice = true := by decide
    refine ⟨c8r1263targets, c8r1263choice, ?_, checked⟩
    intro S h
    simp only [c8r1263targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 30 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1256_closed
  · subst row; exact c8r1257_closed
  · subst row; exact c8r1258_closed
  · subst row; exact c8r1259_closed
  · subst row; exact c8r1260_closed
  · subst row; exact c8r1261_closed
  · subst row; exact c8r1262_closed
  · subst row; exact c8r1263_closed
theorem C8R01248G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1264_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] := by
    let c8r1264targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
    let c8r1264choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1264targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] c8r1264choice = true := by decide
    refine ⟨c8r1264targets, c8r1264choice, ?_, checked⟩
    intro S h
    simp only [c8r1264targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 1 _ (by rfl)))
  have c8r1265_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)] := by
    let c8r1265targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
    let c8r1265choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1265targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)] c8r1265choice = true := by decide
    refine ⟨c8r1265targets, c8r1265choice, ?_, checked⟩
    intro S h
    simp only [c8r1265targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 4 _ (by rfl)))
  have c8r1266_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)] := by
    let c8r1266targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
    let c8r1266choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1266targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)] c8r1266choice = true := by decide
    refine ⟨c8r1266targets, c8r1266choice, ?_, checked⟩
    intro S h
    simp only [c8r1266targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 7 _ (by rfl)))
  have c8r1267_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)] := by
    let c8r1267targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1267choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1267targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)] c8r1267choice = true := by decide
    refine ⟨c8r1267targets, c8r1267choice, ?_, checked⟩
    intro S h
    simp only [c8r1267targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 12 _ (by rfl)))
  have c8r1268_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)] := by
    let c8r1268targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]
    let c8r1268choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1268targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)] c8r1268choice = true := by decide
    refine ⟨c8r1268targets, c8r1268choice, ?_, checked⟩
    intro S h
    simp only [c8r1268targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 14 _ (by rfl)))
  have c8r1269_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)] := by
    let c8r1269targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
    let c8r1269choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1269targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)] c8r1269choice = true := by decide
    refine ⟨c8r1269targets, c8r1269choice, ?_, checked⟩
    intro S h
    simp only [c8r1269targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 16 _ (by rfl)))
  have c8r1270_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)] := by
    let c8r1270targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)]]
    let c8r1270choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1270targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)] c8r1270choice = true := by decide
    refine ⟨c8r1270targets, c8r1270choice, ?_, checked⟩
    intro S h
    simp only [c8r1270targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 20 _ (by rfl)))
  have c8r1271_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)] := by
    let c8r1271targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)]]
    let c8r1271choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1271targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)] c8r1271choice = true := by decide
    refine ⟨c8r1271targets, c8r1271choice, ?_, checked⟩
    intro S h
    simp only [c8r1271targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 23 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1264_closed
  · subst row; exact c8r1265_closed
  · subst row; exact c8r1266_closed
  · subst row; exact c8r1267_closed
  · subst row; exact c8r1268_closed
  · subst row; exact c8r1269_closed
  · subst row; exact c8r1270_closed
  · subst row; exact c8r1271_closed
theorem C8R01248G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1272_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)] := by
    let c8r1272targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)]]
    let c8r1272choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1272targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)] c8r1272choice = true := by decide
    refine ⟨c8r1272targets, c8r1272choice, ?_, checked⟩
    intro S h
    simp only [c8r1272targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 26 _ (by rfl)))
  have c8r1273_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)] := by
    let c8r1273targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)]]
    let c8r1273choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1273targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)] c8r1273choice = true := by decide
    refine ⟨c8r1273targets, c8r1273choice, ?_, checked⟩
    intro S h
    simp only [c8r1273targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 29 _ (by rfl)))
  have c8r1274_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)] := by
    let c8r1274targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)]]
    let c8r1274choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1274targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)] c8r1274choice = true := by decide
    refine ⟨c8r1274targets, c8r1274choice, ?_, checked⟩
    intro S h
    simp only [c8r1274targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 31 _ (by rfl)))
  have c8r1275_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)] := by
    let c8r1275targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1275choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1275targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)] c8r1275choice = true := by decide
    refine ⟨c8r1275targets, c8r1275choice, ?_, checked⟩
    intro S h
    simp only [c8r1275targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 3 _ (by rfl)))
  have c8r1276_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)] := by
    let c8r1276targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)]]
    let c8r1276choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1276targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)] c8r1276choice = true := by decide
    refine ⟨c8r1276targets, c8r1276choice, ?_, checked⟩
    intro S h
    simp only [c8r1276targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 6 _ (by rfl)))
  have c8r1277_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)] := by
    let c8r1277targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)]]
    let c8r1277choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1277targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)] c8r1277choice = true := by decide
    refine ⟨c8r1277targets, c8r1277choice, ?_, checked⟩
    intro S h
    simp only [c8r1277targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 8 _ (by rfl)))
  have c8r1278_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)] := by
    let c8r1278targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1278choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1278targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)] c8r1278choice = true := by decide
    refine ⟨c8r1278targets, c8r1278choice, ?_, checked⟩
    intro S h
    simp only [c8r1278targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L19_lift _ (familyLookup_sound F9B003L19 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 11 _ (by rfl)))
  have c8r1279_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)] := by
    let c8r1279targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)]]
    let c8r1279choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1279targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)] c8r1279choice = true := by decide
    refine ⟨c8r1279targets, c8r1279choice, ?_, checked⟩
    intro S h
    simp only [c8r1279targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L53_lift _ (familyLookup_sound F9B002L53 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L46_lift _ (familyLookup_sound F9B003L46 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L15_lift _ (familyLookup_sound F9B003L15 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L4_lift _ (familyLookup_sound F9B002L4 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 14 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1272_closed
  · subst row; exact c8r1273_closed
  · subst row; exact c8r1274_closed
  · subst row; exact c8r1275_closed
  · subst row; exact c8r1276_closed
  · subst row; exact c8r1277_closed
  · subst row; exact c8r1278_closed
  · subst row; exact c8r1279_closed
theorem C8R01248_closed (row : List GridPoint) (h : FamilyMember row F8B000L39) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L39, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01248G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01248G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01248G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01248G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01248G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01248G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01248G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01248G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01248G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01248G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01248G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01248G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01248G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01248G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01248G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01248G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01248G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01248G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01248G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01248G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01248G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01248G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01248G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01248G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01248G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01248G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01248G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01248G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01248G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01248G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01248G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01248G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
