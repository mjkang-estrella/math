import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01184G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1184_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)] := by
    let c8r1184targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]]
    let c8r1184choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1184targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)] c8r1184choice = true := by decide
    refine ⟨c8r1184targets, c8r1184choice, ?_, checked⟩
    intro S h
    simp only [c8r1184targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 29 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 1 _ (by rfl)))
  have c8r1185_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)] := by
    let c8r1185targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]]
    let c8r1185choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1185targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)] c8r1185choice = true := by decide
    refine ⟨c8r1185targets, c8r1185choice, ?_, checked⟩
    intro S h
    simp only [c8r1185targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 30 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 4 _ (by rfl)))
  have c8r1186_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)] := by
    let c8r1186targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]]
    let c8r1186choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1186targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)] c8r1186choice = true := by decide
    refine ⟨c8r1186targets, c8r1186choice, ?_, checked⟩
    intro S h
    simp only [c8r1186targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L43_lift _ (familyLookup_sound F9B003L43 [] 31 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 6 _ (by rfl)))
  have c8r1187_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)] := by
    let c8r1187targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]]
    let c8r1187choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1187targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)] c8r1187choice = true := by decide
    refine ⟨c8r1187targets, c8r1187choice, ?_, checked⟩
    intro S h
    simp only [c8r1187targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 0 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 9 _ (by rfl)))
  have c8r1188_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)] := by
    let c8r1188targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]]
    let c8r1188choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1188targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)] c8r1188choice = true := by decide
    refine ⟨c8r1188targets, c8r1188choice, ?_, checked⟩
    intro S h
    simp only [c8r1188targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 1 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 12 _ (by rfl)))
  have c8r1189_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)] := by
    let c8r1189targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]]
    let c8r1189choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1189targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)] c8r1189choice = true := by decide
    refine ⟨c8r1189targets, c8r1189choice, ?_, checked⟩
    intro S h
    simp only [c8r1189targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 2 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L20_lift _ (familyLookup_sound F9B004L20 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 15 _ (by rfl)))
  have c8r1190_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)] := by
    let c8r1190targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]]
    let c8r1190choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1190targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)] c8r1190choice = true := by decide
    refine ⟨c8r1190targets, c8r1190choice, ?_, checked⟩
    intro S h
    simp only [c8r1190targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 3 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 18 _ (by rfl)))
  have c8r1191_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5)] := by
    let c8r1191targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,5),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,5)]]
    let c8r1191choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1191targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5)] c8r1191choice = true := by decide
    refine ⟨c8r1191targets, c8r1191choice, ?_, checked⟩
    intro S h
    simp only [c8r1191targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 4 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 24 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1184_closed
  · subst row; exact c8r1185_closed
  · subst row; exact c8r1186_closed
  · subst row; exact c8r1187_closed
  · subst row; exact c8r1188_closed
  · subst row; exact c8r1189_closed
  · subst row; exact c8r1190_closed
  · subst row; exact c8r1191_closed
theorem C8R01184G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1192_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0)] := by
    let c8r1192targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(3,0)]]
    let c8r1192choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1192targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0)] c8r1192choice = true := by decide
    refine ⟨c8r1192targets, c8r1192choice, ?_, checked⟩
    intro S h
    simp only [c8r1192targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 5 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 28 _ (by rfl)))
  have c8r1193_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1)] := by
    let c8r1193targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(3,1)]]
    let c8r1193choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1193targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1)] c8r1193choice = true := by decide
    refine ⟨c8r1193targets, c8r1193choice, ?_, checked⟩
    intro S h
    simp only [c8r1193targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 6 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L56_lift _ (familyLookup_sound F9B001L56 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 0 _ (by rfl)))
  have c8r1194_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3)] := by
    let c8r1194targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3)]]
    let c8r1194choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1194targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3)] c8r1194choice = true := by decide
    refine ⟨c8r1194targets, c8r1194choice, ?_, checked⟩
    intro S h
    simp only [c8r1194targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 7 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 3 _ (by rfl)))
  have c8r1195_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4)] := by
    let c8r1195targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(3,4)]]
    let c8r1195choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1195targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4)] c8r1195choice = true := by decide
    refine ⟨c8r1195targets, c8r1195choice, ?_, checked⟩
    intro S h
    simp only [c8r1195targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 8 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 5 _ (by rfl)))
  have c8r1196_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)] := by
    let c8r1196targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(3,1)]]
    let c8r1196choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1196targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)] c8r1196choice = true := by decide
    refine ⟨c8r1196targets, c8r1196choice, ?_, checked⟩
    intro S h
    simp only [c8r1196targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 9 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 9 _ (by rfl)))
  have c8r1197_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3)] := by
    let c8r1197targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3),(3,3)]]
    let c8r1197choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1197targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3)] c8r1197choice = true := by decide
    refine ⟨c8r1197targets, c8r1197choice, ?_, checked⟩
    intro S h
    simp only [c8r1197targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 10 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 13 _ (by rfl)))
  have c8r1198_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0)] := by
    let c8r1198targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0),(4,0)]]
    let c8r1198choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1198targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0)] c8r1198choice = true := by decide
    refine ⟨c8r1198targets, c8r1198choice, ?_, checked⟩
    intro S h
    simp only [c8r1198targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 11 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 15 _ (by rfl)))
  have c8r1199_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2)] := by
    let c8r1199targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(3,2)]]
    let c8r1199choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1199targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2)] c8r1199choice = true := by decide
    refine ⟨c8r1199targets, c8r1199choice, ?_, checked⟩
    intro S h
    simp only [c8r1199targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 12 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 18 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1192_closed
  · subst row; exact c8r1193_closed
  · subst row; exact c8r1194_closed
  · subst row; exact c8r1195_closed
  · subst row; exact c8r1196_closed
  · subst row; exact c8r1197_closed
  · subst row; exact c8r1198_closed
  · subst row; exact c8r1199_closed
theorem C8R01184G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1200_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3)] := by
    let c8r1200targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,3)]]
    let c8r1200choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1200targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3)] c8r1200choice = true := by decide
    refine ⟨c8r1200targets, c8r1200choice, ?_, checked⟩
    intro S h
    simp only [c8r1200targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 13 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 21 _ (by rfl)))
  have c8r1201_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1)] := by
    let c8r1201targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1),(4,1)]]
    let c8r1201choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1201targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1)] c8r1201choice = true := by decide
    refine ⟨c8r1201targets, c8r1201choice, ?_, checked⟩
    intro S h
    simp only [c8r1201targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 24 _ (by rfl)))
  have c8r1202_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3)] := by
    let c8r1202targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(3,3)]]
    let c8r1202choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1202targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3)] c8r1202choice = true := by decide
    refine ⟨c8r1202targets, c8r1202choice, ?_, checked⟩
    intro S h
    simp only [c8r1202targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 15 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 27 _ (by rfl)))
  have c8r1203_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4)] := by
    let c8r1203targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4),(2,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(3,4)]]
    let c8r1203choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,5),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1203targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4)] c8r1203choice = true := by decide
    refine ⟨c8r1203targets, c8r1203choice, ?_, checked⟩
    intro S h
    simp only [c8r1203targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 16 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 30 _ (by rfl)))
  have c8r1204_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3)] := by
    let c8r1204targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3),(4,3)]]
    let c8r1204choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1204targets [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3)] c8r1204choice = true := by decide
    refine ⟨c8r1204targets, c8r1204choice, ?_, checked⟩
    intro S h
    simp only [c8r1204targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 17 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L10_lift _ (familyLookup_sound F9B003L10 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 1 _ (by rfl)))
  have c8r1205_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)] := by
    let c8r1205targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1205choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1205targets [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)] c8r1205choice = true := by decide
    refine ⟨c8r1205targets, c8r1205choice, ?_, checked⟩
    intro S h
    simp only [c8r1205targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 18 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 5 _ (by rfl)))
  have c8r1206_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)] := by
    let c8r1206targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)]]
    let c8r1206choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1206targets [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)] c8r1206choice = true := by decide
    refine ⟨c8r1206targets, c8r1206choice, ?_, checked⟩
    intro S h
    simp only [c8r1206targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 19 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 7 _ (by rfl)))
  have c8r1207_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)] := by
    let c8r1207targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)]]
    let c8r1207choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1207targets [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)] c8r1207choice = true := by decide
    refine ⟨c8r1207targets, c8r1207choice, ?_, checked⟩
    intro S h
    simp only [c8r1207targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 20 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 9 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1200_closed
  · subst row; exact c8r1201_closed
  · subst row; exact c8r1202_closed
  · subst row; exact c8r1203_closed
  · subst row; exact c8r1204_closed
  · subst row; exact c8r1205_closed
  · subst row; exact c8r1206_closed
  · subst row; exact c8r1207_closed
theorem C8R01184G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1208_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1)] := by
    let c8r1208targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)]]
    let c8r1208choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1208targets [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1)] c8r1208choice = true := by decide
    refine ⟨c8r1208targets, c8r1208choice, ?_, checked⟩
    intro S h
    simp only [c8r1208targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 21 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 12 _ (by rfl)))
  have c8r1209_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0)] := by
    let c8r1209targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(4,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0),(4,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)]]
    let c8r1209choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1209targets [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0)] c8r1209choice = true := by decide
    refine ⟨c8r1209targets, c8r1209choice, ?_, checked⟩
    intro S h
    simp only [c8r1209targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 22 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 14 _ (by rfl)))
  have c8r1210_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3)] := by
    let c8r1210targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1210choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1210targets [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3)] c8r1210choice = true := by decide
    refine ⟨c8r1210targets, c8r1210choice, ?_, checked⟩
    intro S h
    simp only [c8r1210targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 23 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 18 _ (by rfl)))
  have c8r1211_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1)] := by
    let c8r1211targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)]]
    let c8r1211choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1211targets [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1)] c8r1211choice = true := by decide
    refine ⟨c8r1211targets, c8r1211choice, ?_, checked⟩
    intro S h
    simp only [c8r1211targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 24 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L57_lift _ (familyLookup_sound F9B001L57 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 21 _ (by rfl)))
  have c8r1212_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2)] := by
    let c8r1212targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)]]
    let c8r1212choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1212targets [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2)] c8r1212choice = true := by decide
    refine ⟨c8r1212targets, c8r1212choice, ?_, checked⟩
    intro S h
    simp only [c8r1212targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 25 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 23 _ (by rfl)))
  have c8r1213_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1)] := by
    let c8r1213targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1213choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1213targets [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1)] c8r1213choice = true := by decide
    refine ⟨c8r1213targets, c8r1213choice, ?_, checked⟩
    intro S h
    simp only [c8r1213targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 26 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 26 _ (by rfl)))
  have c8r1214_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2)] := by
    let c8r1214targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)]]
    let c8r1214choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1214targets [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2)] c8r1214choice = true := by decide
    refine ⟨c8r1214targets, c8r1214choice, ?_, checked⟩
    intro S h
    simp only [c8r1214targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 27 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 29 _ (by rfl)))
  have c8r1215_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1)] := by
    let c8r1215targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)]]
    let c8r1215choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1215targets [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1)] c8r1215choice = true := by decide
    refine ⟨c8r1215targets, c8r1215choice, ?_, checked⟩
    intro S h
    simp only [c8r1215targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 28 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 0 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1208_closed
  · subst row; exact c8r1209_closed
  · subst row; exact c8r1210_closed
  · subst row; exact c8r1211_closed
  · subst row; exact c8r1212_closed
  · subst row; exact c8r1213_closed
  · subst row; exact c8r1214_closed
  · subst row; exact c8r1215_closed
theorem C8R01184_closed (row : List GridPoint) (h : FamilyMember row F8B000L37) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L37, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01184G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01184G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01184G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01184G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01184G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01184G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01184G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01184G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01184G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01184G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01184G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01184G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01184G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01184G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01184G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01184G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01184G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01184G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01184G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01184G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01184G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01184G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01184G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01184G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01184G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01184G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01184G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01184G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01184G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01184G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01184G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01184G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
