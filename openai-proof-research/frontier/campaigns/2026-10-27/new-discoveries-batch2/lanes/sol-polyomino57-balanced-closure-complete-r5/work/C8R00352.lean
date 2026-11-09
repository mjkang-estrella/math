import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00352G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r352_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r352targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r352choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r352targets [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2)] c8r352choice = true := by decide
    refine ⟨c8r352targets, c8r352choice, ?_, checked⟩
    intro S h
    simp only [c8r352targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L39_lift _ (familyLookup_sound F9B003L39 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 16 _ (by rfl)))
  have c8r353_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r353targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r353choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r353targets [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,3)] c8r353choice = true := by decide
    refine ⟨c8r353targets, c8r353choice, ?_, checked⟩
    intro S h
    simp only [c8r353targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 18 _ (by rfl)))
  have c8r354_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r354targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r354choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r354targets [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1)] c8r354choice = true := by decide
    refine ⟨c8r354targets, c8r354choice, ?_, checked⟩
    intro S h
    simp only [c8r354targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 21 _ (by rfl)))
  have c8r355_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2)] := by
    let c8r355targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c8r355choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r355targets [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2)] c8r355choice = true := by decide
    refine ⟨c8r355targets, c8r355choice, ?_, checked⟩
    intro S h
    simp only [c8r355targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 24 _ (by rfl)))
  have c8r356_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1)] := by
    let c8r356targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c8r356choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r356targets [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1)] c8r356choice = true := by decide
    refine ⟨c8r356targets, c8r356choice, ?_, checked⟩
    intro S h
    simp only [c8r356targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 27 _ (by rfl)))
  have c8r357_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3)] := by
    let c8r357targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c8r357choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r357targets [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3)] c8r357choice = true := by decide
    refine ⟨c8r357targets, c8r357choice, ?_, checked⟩
    intro S h
    simp only [c8r357targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 30 _ (by rfl)))
  have c8r358_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2)] := by
    let c8r358targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c8r358choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r358targets [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2)] c8r358choice = true := by decide
    refine ⟨c8r358targets, c8r358choice, ?_, checked⟩
    intro S h
    simp only [c8r358targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 1 _ (by rfl)))
  have c8r359_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5)] := by
    let c8r359targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c8r359choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((1,5),(9,(0,0))),((2,1),(10,(0,0))),((2,6),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0))),((3,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r359targets [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5)] c8r359choice = true := by decide
    refine ⟨c8r359targets, c8r359choice, ?_, checked⟩
    intro S h
    simp only [c8r359targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 6 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r352_closed
  · subst row; exact c8r353_closed
  · subst row; exact c8r354_closed
  · subst row; exact c8r355_closed
  · subst row; exact c8r356_closed
  · subst row; exact c8r357_closed
  · subst row; exact c8r358_closed
  · subst row; exact c8r359_closed
theorem C8R00352G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r360_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2)] := by
    let c8r360targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c8r360choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,5),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r360targets [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2)] c8r360choice = true := by decide
    refine ⟨c8r360targets, c8r360choice, ?_, checked⟩
    intro S h
    simp only [c8r360targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 10 _ (by rfl)))
  have c8r361_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3)] := by
    let c8r361targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c8r361choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,5),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r361targets [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3)] c8r361choice = true := by decide
    refine ⟨c8r361targets, c8r361choice, ?_, checked⟩
    intro S h
    simp only [c8r361targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 12 _ (by rfl)))
  have c8r362_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4)] := by
    let c8r362targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c8r362choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,5),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,5),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r362targets [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4)] c8r362choice = true := by decide
    refine ⟨c8r362targets, c8r362choice, ?_, checked⟩
    intro S h
    simp only [c8r362targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 14 _ (by rfl)))
  have c8r363_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2)] := by
    let c8r363targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c8r363choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r363targets [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2)] c8r363choice = true := by decide
    refine ⟨c8r363targets, c8r363choice, ?_, checked⟩
    intro S h
    simp only [c8r363targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 18 _ (by rfl)))
  have c8r364_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3)] := by
    let c8r364targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c8r364choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r364targets [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3)] c8r364choice = true := by decide
    refine ⟨c8r364targets, c8r364choice, ?_, checked⟩
    intro S h
    simp only [c8r364targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 21 _ (by rfl)))
  have c8r365_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2)] := by
    let c8r365targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c8r365choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r365targets [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2)] c8r365choice = true := by decide
    refine ⟨c8r365targets, c8r365choice, ?_, checked⟩
    intro S h
    simp only [c8r365targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 24 _ (by rfl)))
  have c8r366_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4)] := by
    let c8r366targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c8r366choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,5),(11,(0,0))),((4,3),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r366targets [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4)] c8r366choice = true := by decide
    refine ⟨c8r366targets, c8r366choice, ?_, checked⟩
    intro S h
    simp only [c8r366targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 27 _ (by rfl)))
  have c8r367_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(4,3)] := by
    let c8r367targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c8r367choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r367targets [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(4,3)] c8r367choice = true := by decide
    refine ⟨c8r367targets, c8r367choice, ?_, checked⟩
    intro S h
    simp only [c8r367targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 30 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r360_closed
  · subst row; exact c8r361_closed
  · subst row; exact c8r362_closed
  · subst row; exact c8r363_closed
  · subst row; exact c8r364_closed
  · subst row; exact c8r365_closed
  · subst row; exact c8r366_closed
  · subst row; exact c8r367_closed
theorem C8R00352G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r368_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r368targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r368choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,3),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r368targets [(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2)] c8r368choice = true := by decide
    refine ⟨c8r368targets, c8r368choice, ?_, checked⟩
    intro S h
    simp only [c8r368targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 3 _ (by rfl)))
  have c8r369_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3)] := by
    let c8r369targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c8r369choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,4),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r369targets [(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3)] c8r369choice = true := by decide
    refine ⟨c8r369targets, c8r369choice, ?_, checked⟩
    intro S h
    simp only [c8r369targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 7 _ (by rfl)))
  have c8r370_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1)] := by
    let c8r370targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c8r370choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r370targets [(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1)] c8r370choice = true := by decide
    refine ⟨c8r370targets, c8r370choice, ?_, checked⟩
    intro S h
    simp only [c8r370targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 10 _ (by rfl)))
  have c8r371_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2)] := by
    let c8r371targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c8r371choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r371targets [(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2)] c8r371choice = true := by decide
    refine ⟨c8r371targets, c8r371choice, ?_, checked⟩
    intro S h
    simp only [c8r371targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 12 _ (by rfl)))
  have c8r372_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4)] := by
    let c8r372targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c8r372choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,5),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r372targets [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4)] c8r372choice = true := by decide
    refine ⟨c8r372targets, c8r372choice, ?_, checked⟩
    intro S h
    simp only [c8r372targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 16 _ (by rfl)))
  have c8r373_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2)] := by
    let c8r373targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c8r373choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r373targets [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2)] c8r373choice = true := by decide
    refine ⟨c8r373targets, c8r373choice, ?_, checked⟩
    intro S h
    simp only [c8r373targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 19 _ (by rfl)))
  have c8r374_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3)] := by
    let c8r374targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c8r374choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r374targets [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3)] c8r374choice = true := by decide
    refine ⟨c8r374targets, c8r374choice, ?_, checked⟩
    intro S h
    simp only [c8r374targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L30_lift _ (familyLookup_sound F9B001L30 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 21 _ (by rfl)))
  have c8r375_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2)] := by
    let c8r375targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c8r375choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,3),(13,(0,0))),((5,1),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r375targets [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2)] c8r375choice = true := by decide
    refine ⟨c8r375targets, c8r375choice, ?_, checked⟩
    intro S h
    simp only [c8r375targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 25 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r368_closed
  · subst row; exact c8r369_closed
  · subst row; exact c8r370_closed
  · subst row; exact c8r371_closed
  · subst row; exact c8r372_closed
  · subst row; exact c8r373_closed
  · subst row; exact c8r374_closed
  · subst row; exact c8r375_closed
theorem C8R00352G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r376_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3)] := by
    let c8r376targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c8r376choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,4),(13,(0,0))),((5,2),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r376targets [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3)] c8r376choice = true := by decide
    refine ⟨c8r376targets, c8r376choice, ?_, checked⟩
    intro S h
    simp only [c8r376targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 28 _ (by rfl)))
  have c8r377_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2)] := by
    let c8r377targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c8r377choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,1),(14,(0,0))),((5,3),(15,(0,0))),((6,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r377targets [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2)] c8r377choice = true := by decide
    refine ⟨c8r377targets, c8r377choice, ?_, checked⟩
    intro S h
    simp only [c8r377targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L25_lift _ (familyLookup_sound F9B000L25 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 31 _ (by rfl)))
  have c8r378_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)] := by
    let c8r378targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,5),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,3)]]
    let c8r378choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((-1,5),(4,(1,0))),((0,-1),(5,(0,1))),((0,2),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,4),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r378targets [(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)] c8r378choice = true := by decide
    refine ⟨c8r378targets, c8r378choice, ?_, checked⟩
    intro S h
    simp only [c8r378targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 1 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 14 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 15 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 6 _ (by rfl)))
  have c8r379_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)] := by
    let c8r379targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)]]
    let c8r379choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,2),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r379targets [(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)] c8r379choice = true := by decide
    refine ⟨c8r379targets, c8r379choice, ?_, checked⟩
    intro S h
    simp only [c8r379targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 2 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 15 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 11 _ (by rfl)))
  have c8r380_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r380targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r380choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,2),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r380targets [(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)] c8r380choice = true := by decide
    refine ⟨c8r380targets, c8r380choice, ?_, checked⟩
    intro S h
    simp only [c8r380targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 3 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 16 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 16 _ (by rfl)))
  have c8r381_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1)] := by
    let c8r381targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,1)]]
    let c8r381choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,2),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r381targets [(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1)] c8r381choice = true := by decide
    refine ⟨c8r381targets, c8r381choice, ?_, checked⟩
    intro S h
    simp only [c8r381targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 4 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 17 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 20 _ (by rfl)))
  have c8r382_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2)] := by
    let c8r382targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,2)]]
    let c8r382choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,2),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r382targets [(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2)] c8r382choice = true := by decide
    refine ⟨c8r382targets, c8r382choice, ?_, checked⟩
    intro S h
    simp only [c8r382targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 5 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 18 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 22 _ (by rfl)))
  have c8r383_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3)] := by
    let c8r383targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3),(3,3)]]
    let c8r383choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,2),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r383targets [(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3)] c8r383choice = true := by decide
    refine ⟨c8r383targets, c8r383choice, ?_, checked⟩
    intro S h
    simp only [c8r383targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 6 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 19 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 24 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r376_closed
  · subst row; exact c8r377_closed
  · subst row; exact c8r378_closed
  · subst row; exact c8r379_closed
  · subst row; exact c8r380_closed
  · subst row; exact c8r381_closed
  · subst row; exact c8r382_closed
  · subst row; exact c8r383_closed
theorem C8R00352_closed (row : List GridPoint) (h : FamilyMember row F8B000L11) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L11, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00352G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00352G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00352G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00352G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00352G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00352G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00352G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00352G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00352G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00352G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00352G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00352G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00352G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00352G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00352G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00352G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00352G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00352G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00352G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00352G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00352G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00352G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00352G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00352G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00352G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00352G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00352G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00352G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00352G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00352G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00352G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00352G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
