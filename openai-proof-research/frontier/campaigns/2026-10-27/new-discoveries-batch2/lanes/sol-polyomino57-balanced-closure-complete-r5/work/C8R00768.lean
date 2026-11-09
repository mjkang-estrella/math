import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00768G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r768_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c8r768targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c8r768choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r768targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] c8r768choice = true := by decide
    refine ⟨c8r768targets, c8r768choice, ?_, checked⟩
    intro S h
    simp only [c8r768targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 9 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 5 _ (by rfl)))
  have c8r769_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c8r769targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c8r769choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r769targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] c8r769choice = true := by decide
    refine ⟨c8r769targets, c8r769choice, ?_, checked⟩
    intro S h
    simp only [c8r769targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 10 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L25_lift _ (familyLookup_sound F9B002L25 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 7 _ (by rfl)))
  have c8r770_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r770targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r770choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r770targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] c8r770choice = true := by decide
    refine ⟨c8r770targets, c8r770choice, ?_, checked⟩
    intro S h
    simp only [c8r770targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 11 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 9 _ (by rfl)))
  have c8r771_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c8r771targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c8r771choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r771targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] c8r771choice = true := by decide
    refine ⟨c8r771targets, c8r771choice, ?_, checked⟩
    intro S h
    simp only [c8r771targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 12 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 13 _ (by rfl)))
  have c8r772_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] := by
    let c8r772targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)]]
    let c8r772choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r772targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] c8r772choice = true := by decide
    refine ⟨c8r772targets, c8r772choice, ?_, checked⟩
    intro S h
    simp only [c8r772targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 13 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 16 _ (by rfl)))
  have c8r773_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] := by
    let c8r773targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)]]
    let c8r773choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r773targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] c8r773choice = true := by decide
    refine ⟨c8r773targets, c8r773choice, ?_, checked⟩
    intro S h
    simp only [c8r773targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 14 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 19 _ (by rfl)))
  have c8r774_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] := by
    let c8r774targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)]]
    let c8r774choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,-1),(12,(0,1))),((3,1),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r774targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] c8r774choice = true := by decide
    refine ⟨c8r774targets, c8r774choice, ?_, checked⟩
    intro S h
    simp only [c8r774targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 15 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 21 _ (by rfl)))
  have c8r775_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] := by
    let c8r775targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
    let c8r775choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r775targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] c8r775choice = true := by decide
    refine ⟨c8r775targets, c8r775choice, ?_, checked⟩
    intro S h
    simp only [c8r775targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 16 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 24 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r768_closed
  · subst row; exact c8r769_closed
  · subst row; exact c8r770_closed
  · subst row; exact c8r771_closed
  · subst row; exact c8r772_closed
  · subst row; exact c8r773_closed
  · subst row; exact c8r774_closed
  · subst row; exact c8r775_closed
theorem C8R00768G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r776_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] := by
    let c8r776targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
    let c8r776choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r776targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] c8r776choice = true := by decide
    refine ⟨c8r776targets, c8r776choice, ?_, checked⟩
    intro S h
    simp only [c8r776targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 17 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 27 _ (by rfl)))
  have c8r777_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] := by
    let c8r777targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
    let c8r777choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r777targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] c8r777choice = true := by decide
    refine ⟨c8r777targets, c8r777choice, ?_, checked⟩
    intro S h
    simp only [c8r777targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 18 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 30 _ (by rfl)))
  have c8r778_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] := by
    let c8r778targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
    let c8r778choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r778targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] c8r778choice = true := by decide
    refine ⟨c8r778targets, c8r778choice, ?_, checked⟩
    intro S h
    simp only [c8r778targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 19 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 1 _ (by rfl)))
  have c8r779_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] := by
    let c8r779targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
    let c8r779choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r779targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] c8r779choice = true := by decide
    refine ⟨c8r779targets, c8r779choice, ?_, checked⟩
    intro S h
    simp only [c8r779targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 20 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 4 _ (by rfl)))
  have c8r780_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)] := by
    let c8r780targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
    let c8r780choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,5),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r780targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)] c8r780choice = true := by decide
    refine ⟨c8r780targets, c8r780choice, ?_, checked⟩
    intro S h
    simp only [c8r780targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 21 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 7 _ (by rfl)))
  have c8r781_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)] := by
    let c8r781targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
    let c8r781choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r781targets [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)] c8r781choice = true := by decide
    refine ⟨c8r781targets, c8r781choice, ?_, checked⟩
    intro S h
    simp only [c8r781targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 22 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 10 _ (by rfl)))
  have c8r782_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)] := by
    let c8r782targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c8r782choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r782targets [(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)] c8r782choice = true := by decide
    refine ⟨c8r782targets, c8r782choice, ?_, checked⟩
    intro S h
    simp only [c8r782targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 23 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 16 _ (by rfl)))
  have c8r783_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c8r783targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,4),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c8r783choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r783targets [(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] c8r783choice = true := by decide
    refine ⟨c8r783targets, c8r783choice, ?_, checked⟩
    intro S h
    simp only [c8r783targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 24 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L16_lift _ (familyLookup_sound F9B001L16 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 21 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r776_closed
  · subst row; exact c8r777_closed
  · subst row; exact c8r778_closed
  · subst row; exact c8r779_closed
  · subst row; exact c8r780_closed
  · subst row; exact c8r781_closed
  · subst row; exact c8r782_closed
  · subst row; exact c8r783_closed
theorem C8R00768G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r784_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r784targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,4),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r784choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0))),((3,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r784targets [(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)] c8r784choice = true := by decide
    refine ⟨c8r784targets, c8r784choice, ?_, checked⟩
    intro S h
    simp only [c8r784targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 25 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L19_lift _ (familyLookup_sound F9B004L19 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 27 _ (by rfl)))
  have c8r785_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r785targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,5),(1,0),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r785choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,4),(1,(1,0))),((-1,5),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,2),(5,(0,0))),((0,3),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0))),((2,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r785targets [(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)] c8r785choice = true := by decide
    refine ⟨c8r785targets, c8r785choice, ?_, checked⟩
    intro S h
    simp only [c8r785targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 26 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 9 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 2 _ (by rfl)))
  have c8r786_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r786targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r786choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,4),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r786targets [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r786choice = true := by decide
    refine ⟨c8r786targets, c8r786choice, ?_, checked⟩
    intro S h
    simp only [c8r786targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 27 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L26_lift _ (familyLookup_sound F9B002L26 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 9 _ (by rfl)))
  have c8r787_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] := by
    let c8r787targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
    let c8r787choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,4),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,5),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((3,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r787targets [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] c8r787choice = true := by decide
    refine ⟨c8r787targets, c8r787choice, ?_, checked⟩
    intro S h
    simp only [c8r787targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 28 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 14 _ (by rfl)))
  have c8r788_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c8r788targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c8r788choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,4),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r788targets [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] c8r788choice = true := by decide
    refine ⟨c8r788targets, c8r788choice, ?_, checked⟩
    intro S h
    simp only [c8r788targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 29 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 18 _ (by rfl)))
  have c8r789_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c8r789targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c8r789choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,4),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r789targets [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] c8r789choice = true := by decide
    refine ⟨c8r789targets, c8r789choice, ?_, checked⟩
    intro S h
    simp only [c8r789targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 30 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 21 _ (by rfl)))
  have c8r790_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c8r790targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c8r790choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,4),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r790targets [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] c8r790choice = true := by decide
    refine ⟨c8r790targets, c8r790choice, ?_, checked⟩
    intro S h
    simp only [c8r790targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L43_lift _ (familyLookup_sound F9B001L43 [] 31 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 23 _ (by rfl)))
  have c8r791_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r791targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r791choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,4),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r791targets [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] c8r791choice = true := by decide
    refine ⟨c8r791targets, c8r791choice, ?_, checked⟩
    intro S h
    simp only [c8r791targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 0 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L42_lift _ (familyLookup_sound F9B000L42 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 25 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r784_closed
  · subst row; exact c8r785_closed
  · subst row; exact c8r786_closed
  · subst row; exact c8r787_closed
  · subst row; exact c8r788_closed
  · subst row; exact c8r789_closed
  · subst row; exact c8r790_closed
  · subst row; exact c8r791_closed
theorem C8R00768G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r792_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r792targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,5),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r792choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,5),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,4),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,6),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0))),((2,4),(14,(0,0))),((2,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r792targets [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r792choice = true := by decide
    refine ⟨c8r792targets, c8r792choice, ?_, checked⟩
    intro S h
    simp only [c8r792targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 1 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 7 _ (by rfl)))
  have c8r793_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] := by
    let c8r793targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)]]
    let c8r793choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,7),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0))),((2,4),(14,(0,0))),((2,5),(15,(0,0))),((2,6),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r793targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] c8r793choice = true := by decide
    refine ⟨c8r793targets, c8r793choice, ?_, checked⟩
    intro S h
    simp only [c8r793targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 16 _ (by rfl)))
  have c8r794_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)] := by
    let c8r794targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)]]
    let c8r794choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((3,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r794targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)] c8r794choice = true := by decide
    refine ⟨c8r794targets, c8r794choice, ?_, checked⟩
    intro S h
    simp only [c8r794targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L49_lift _ (familyLookup_sound F9B002L49 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 22 _ (by rfl)))
  have c8r795_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)] := by
    let c8r795targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)]]
    let c8r795choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0))),((3,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r795targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)] c8r795choice = true := by decide
    refine ⟨c8r795targets, c8r795choice, ?_, checked⟩
    intro S h
    simp only [c8r795targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 27 _ (by rfl)))
  have c8r796_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)] := by
    let c8r796targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)]]
    let c8r796choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0))),((3,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r796targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)] c8r796choice = true := by decide
    refine ⟨c8r796targets, c8r796choice, ?_, checked⟩
    intro S h
    simp only [c8r796targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 31 _ (by rfl)))
  have c8r797_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)] := by
    let c8r797targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)]]
    let c8r797choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r797targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)] c8r797choice = true := by decide
    refine ⟨c8r797targets, c8r797choice, ?_, checked⟩
    intro S h
    simp only [c8r797targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 2 _ (by rfl)))
  have c8r798_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)] := by
    let c8r798targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)]]
    let c8r798choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r798targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)] c8r798choice = true := by decide
    refine ⟨c8r798targets, c8r798choice, ?_, checked⟩
    intro S h
    simp only [c8r798targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 4 _ (by rfl)))
  have c8r799_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)] := by
    let c8r799targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)]]
    let c8r799choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,6),(14,(0,0))),((3,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r799targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)] c8r799choice = true := by decide
    refine ⟨c8r799targets, c8r799choice, ?_, checked⟩
    intro S h
    simp only [c8r799targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L44_lift _ (familyLookup_sound F9B001L44 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L54_lift _ (familyLookup_sound F9B000L54 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L10_lift _ (familyLookup_sound F9B001L10 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L15_lift _ (familyLookup_sound F9B001L15 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 6 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r792_closed
  · subst row; exact c8r793_closed
  · subst row; exact c8r794_closed
  · subst row; exact c8r795_closed
  · subst row; exact c8r796_closed
  · subst row; exact c8r797_closed
  · subst row; exact c8r798_closed
  · subst row; exact c8r799_closed
theorem C8R00768_closed (row : List GridPoint) (h : FamilyMember row F8B000L24) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L24, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00768G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00768G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00768G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00768G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00768G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00768G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00768G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00768G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00768G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00768G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00768G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00768G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00768G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00768G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00768G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00768G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00768G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00768G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00768G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00768G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00768G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00768G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00768G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00768G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00768G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00768G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00768G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00768G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00768G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00768G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00768G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00768G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
