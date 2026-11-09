import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00384G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r384_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r384targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r384choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r384targets [(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)] c8r384choice = true := by decide
    refine ⟨c8r384targets, c8r384choice, ?_, checked⟩
    intro S h
    simp only [c8r384targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 7 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 0 _ (by rfl)))
  have c8r385_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)] := by
    let c8r385targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
    let c8r385choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r385targets [(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)] c8r385choice = true := by decide
    refine ⟨c8r385targets, c8r385choice, ?_, checked⟩
    intro S h
    simp only [c8r385targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 8 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 4 _ (by rfl)))
  have c8r386_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)] := by
    let c8r386targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
    let c8r386choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r386targets [(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)] c8r386choice = true := by decide
    refine ⟨c8r386targets, c8r386choice, ?_, checked⟩
    intro S h
    simp only [c8r386targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 9 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 7 _ (by rfl)))
  have c8r387_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)] := by
    let c8r387targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
    let c8r387choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r387targets [(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)] c8r387choice = true := by decide
    refine ⟨c8r387targets, c8r387choice, ?_, checked⟩
    intro S h
    simp only [c8r387targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 10 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 9 _ (by rfl)))
  have c8r388_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)] := by
    let c8r388targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
    let c8r388choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r388targets [(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)] c8r388choice = true := by decide
    refine ⟨c8r388targets, c8r388choice, ?_, checked⟩
    intro S h
    simp only [c8r388targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 11 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 11 _ (by rfl)))
  have c8r389_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r389targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r389choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,6),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r389targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r389choice = true := by decide
    refine ⟨c8r389targets, c8r389choice, ?_, checked⟩
    intro S h
    simp only [c8r389targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 12 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 20 _ (by rfl)))
  have c8r390_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c8r390targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c8r390choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r390targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)] c8r390choice = true := by decide
    refine ⟨c8r390targets, c8r390choice, ?_, checked⟩
    intro S h
    simp only [c8r390targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 13 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 25 _ (by rfl)))
  have c8r391_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c8r391targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c8r391choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r391targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)] c8r391choice = true := by decide
    refine ⟨c8r391targets, c8r391choice, ?_, checked⟩
    intro S h
    simp only [c8r391targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 14 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 28 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r384_closed
  · subst row; exact c8r385_closed
  · subst row; exact c8r386_closed
  · subst row; exact c8r387_closed
  · subst row; exact c8r388_closed
  · subst row; exact c8r389_closed
  · subst row; exact c8r390_closed
  · subst row; exact c8r391_closed
theorem C8R00384G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r392_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c8r392targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c8r392choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r392targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)] c8r392choice = true := by decide
    refine ⟨c8r392targets, c8r392choice, ?_, checked⟩
    intro S h
    simp only [c8r392targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 15 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 30 _ (by rfl)))
  have c8r393_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r393targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r393choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r393targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)] c8r393choice = true := by decide
    refine ⟨c8r393targets, c8r393choice, ?_, checked⟩
    intro S h
    simp only [c8r393targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 16 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 0 _ (by rfl)))
  have c8r394_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c8r394targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c8r394choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r394targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)] c8r394choice = true := by decide
    refine ⟨c8r394targets, c8r394choice, ?_, checked⟩
    intro S h
    simp only [c8r394targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 17 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 4 _ (by rfl)))
  have c8r395_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)] := by
    let c8r395targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
    let c8r395choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r395targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)] c8r395choice = true := by decide
    refine ⟨c8r395targets, c8r395choice, ?_, checked⟩
    intro S h
    simp only [c8r395targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 18 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 7 _ (by rfl)))
  have c8r396_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)] := by
    let c8r396targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
    let c8r396choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r396targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)] c8r396choice = true := by decide
    refine ⟨c8r396targets, c8r396choice, ?_, checked⟩
    intro S h
    simp only [c8r396targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 19 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 10 _ (by rfl)))
  have c8r397_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)] := by
    let c8r397targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
    let c8r397choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r397targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)] c8r397choice = true := by decide
    refine ⟨c8r397targets, c8r397choice, ?_, checked⟩
    intro S h
    simp only [c8r397targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 20 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 13 _ (by rfl)))
  have c8r398_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)] := by
    let c8r398targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
    let c8r398choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r398targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)] c8r398choice = true := by decide
    refine ⟨c8r398targets, c8r398choice, ?_, checked⟩
    intro S h
    simp only [c8r398targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 21 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 16 _ (by rfl)))
  have c8r399_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2)] := by
    let c8r399targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
    let c8r399choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r399targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2)] c8r399choice = true := by decide
    refine ⟨c8r399targets, c8r399choice, ?_, checked⟩
    intro S h
    simp only [c8r399targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 22 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 19 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r392_closed
  · subst row; exact c8r393_closed
  · subst row; exact c8r394_closed
  · subst row; exact c8r395_closed
  · subst row; exact c8r396_closed
  · subst row; exact c8r397_closed
  · subst row; exact c8r398_closed
  · subst row; exact c8r399_closed
theorem C8R00384G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r400_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4)] := by
    let c8r400targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
    let c8r400choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r400targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4)] c8r400choice = true := by decide
    refine ⟨c8r400targets, c8r400choice, ?_, checked⟩
    intro S h
    simp only [c8r400targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 23 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 22 _ (by rfl)))
  have c8r401_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3)] := by
    let c8r401targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
    let c8r401choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r401targets [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3)] c8r401choice = true := by decide
    refine ⟨c8r401targets, c8r401choice, ?_, checked⟩
    intro S h
    simp only [c8r401targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 24 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 25 _ (by rfl)))
  have c8r402_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)] := by
    let c8r402targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c8r402choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r402targets [(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)] c8r402choice = true := by decide
    refine ⟨c8r402targets, c8r402choice, ?_, checked⟩
    intro S h
    simp only [c8r402targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 25 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 31 _ (by rfl)))
  have c8r403_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r403targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,5),(1,0),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r403choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,4),(2,(1,0))),((-1,5),(3,(1,0))),((0,-1),(4,(0,1))),((0,2),(5,(0,0))),((0,3),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,5),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r403targets [(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)] c8r403choice = true := by decide
    refine ⟨c8r403targets, c8r403choice, ?_, checked⟩
    intro S h
    simp only [c8r403targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 26 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 21 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 6 _ (by rfl)))
  have c8r404_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r404targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r404choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r404targets [(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)] c8r404choice = true := by decide
    refine ⟨c8r404targets, c8r404choice, ?_, checked⟩
    intro S h
    simp only [c8r404targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 27 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 12 _ (by rfl)))
  have c8r405_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r405targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r405choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,6),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r405targets [(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r405choice = true := by decide
    refine ⟨c8r405targets, c8r405choice, ?_, checked⟩
    intro S h
    simp only [c8r405targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 28 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 18 _ (by rfl)))
  have c8r406_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c8r406targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c8r406choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r406targets [(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)] c8r406choice = true := by decide
    refine ⟨c8r406targets, c8r406choice, ?_, checked⟩
    intro S h
    simp only [c8r406targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 29 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 23 _ (by rfl)))
  have c8r407_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c8r407targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c8r407choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r407targets [(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)] c8r407choice = true := by decide
    refine ⟨c8r407targets, c8r407choice, ?_, checked⟩
    intro S h
    simp only [c8r407targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 30 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 26 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r400_closed
  · subst row; exact c8r401_closed
  · subst row; exact c8r402_closed
  · subst row; exact c8r403_closed
  · subst row; exact c8r404_closed
  · subst row; exact c8r405_closed
  · subst row; exact c8r406_closed
  · subst row; exact c8r407_closed
theorem C8R00384G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r408_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c8r408targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c8r408choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r408targets [(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)] c8r408choice = true := by decide
    refine ⟨c8r408targets, c8r408choice, ?_, checked⟩
    intro S h
    simp only [c8r408targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 31 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 28 _ (by rfl)))
  have c8r409_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r409targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r409choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r409targets [(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)] c8r409choice = true := by decide
    refine ⟨c8r409targets, c8r409choice, ?_, checked⟩
    intro S h
    simp only [c8r409targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 0 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 30 _ (by rfl)))
  have c8r410_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r410targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,5),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r410choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,5),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,4),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,6),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r410targets [(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r410choice = true := by decide
    refine ⟨c8r410targets, c8r410choice, ?_, checked⟩
    intro S h
    simp only [c8r410targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 1 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 9 _ (by rfl)))
  have c8r411_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r411targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r411choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r411targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r411choice = true := by decide
    refine ⟨c8r411targets, c8r411choice, ?_, checked⟩
    intro S h
    simp only [c8r411targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 17 _ (by rfl)))
  have c8r412_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] := by
    let c8r412targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
    let c8r412choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r412targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] c8r412choice = true := by decide
    refine ⟨c8r412targets, c8r412choice, ?_, checked⟩
    intro S h
    simp only [c8r412targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L10_lift _ (familyLookup_sound F9B002L10 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 22 _ (by rfl)))
  have c8r413_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c8r413targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c8r413choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r413targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] c8r413choice = true := by decide
    refine ⟨c8r413targets, c8r413choice, ?_, checked⟩
    intro S h
    simp only [c8r413targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 26 _ (by rfl)))
  have c8r414_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c8r414targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c8r414choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r414targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] c8r414choice = true := by decide
    refine ⟨c8r414targets, c8r414choice, ?_, checked⟩
    intro S h
    simp only [c8r414targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 29 _ (by rfl)))
  have c8r415_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c8r415targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c8r415choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r415targets [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] c8r415choice = true := by decide
    refine ⟨c8r415targets, c8r415choice, ?_, checked⟩
    intro S h
    simp only [c8r415targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L40_lift _ (familyLookup_sound F9B002L40 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L27_lift _ (familyLookup_sound F9B000L27 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L3_lift _ (familyLookup_sound F9B002L3 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 31 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r408_closed
  · subst row; exact c8r409_closed
  · subst row; exact c8r410_closed
  · subst row; exact c8r411_closed
  · subst row; exact c8r412_closed
  · subst row; exact c8r413_closed
  · subst row; exact c8r414_closed
  · subst row; exact c8r415_closed
theorem C8R00384_closed (row : List GridPoint) (h : FamilyMember row F8B000L12) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L12, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00384G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00384G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00384G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00384G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00384G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00384G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00384G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00384G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00384G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00384G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00384G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00384G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00384G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00384G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00384G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00384G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00384G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00384G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00384G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00384G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00384G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00384G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00384G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00384G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00384G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00384G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00384G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00384G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00384G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00384G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00384G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00384G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
