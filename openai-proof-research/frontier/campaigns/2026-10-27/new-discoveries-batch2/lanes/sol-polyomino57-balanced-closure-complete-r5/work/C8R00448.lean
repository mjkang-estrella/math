import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00448G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r448_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)] := by
    let c8r448targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c8r448choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r448targets [(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)] c8r448choice = true := by decide
    refine ⟨c8r448targets, c8r448choice, ?_, checked⟩
    intro S h
    simp only [c8r448targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L40_lift _ (familyLookup_sound F9B000L40 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L5_lift _ (familyLookup_sound F9B002L5 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L44_lift _ (familyLookup_sound F9B000L44 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 5 _ (by rfl)))
  have c8r449_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r449targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r449choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r449targets [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)] c8r449choice = true := by decide
    refine ⟨c8r449targets, c8r449choice, ?_, checked⟩
    intro S h
    simp only [c8r449targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 11 _ (by rfl)))
  have c8r450_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r450targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r450choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r450targets [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)] c8r450choice = true := by decide
    refine ⟨c8r450targets, c8r450choice, ?_, checked⟩
    intro S h
    simp only [c8r450targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 14 _ (by rfl)))
  have c8r451_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r451targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r451choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r451targets [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)] c8r451choice = true := by decide
    refine ⟨c8r451targets, c8r451choice, ?_, checked⟩
    intro S h
    simp only [c8r451targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 16 _ (by rfl)))
  have c8r452_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r452targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r452choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r452targets [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)] c8r452choice = true := by decide
    refine ⟨c8r452targets, c8r452choice, ?_, checked⟩
    intro S h
    simp only [c8r452targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 18 _ (by rfl)))
  have c8r453_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)] := by
    let c8r453targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c8r453choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r453targets [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)] c8r453choice = true := by decide
    refine ⟨c8r453targets, c8r453choice, ?_, checked⟩
    intro S h
    simp only [c8r453targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 21 _ (by rfl)))
  have c8r454_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)] := by
    let c8r454targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c8r454choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r454targets [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)] c8r454choice = true := by decide
    refine ⟨c8r454targets, c8r454choice, ?_, checked⟩
    intro S h
    simp only [c8r454targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 23 _ (by rfl)))
  have c8r455_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)] := by
    let c8r455targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c8r455choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r455targets [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)] c8r455choice = true := by decide
    refine ⟨c8r455targets, c8r455choice, ?_, checked⟩
    intro S h
    simp only [c8r455targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 26 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r448_closed
  · subst row; exact c8r449_closed
  · subst row; exact c8r450_closed
  · subst row; exact c8r451_closed
  · subst row; exact c8r452_closed
  · subst row; exact c8r453_closed
  · subst row; exact c8r454_closed
  · subst row; exact c8r455_closed
theorem C8R00448G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r456_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)] := by
    let c8r456targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c8r456choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r456targets [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)] c8r456choice = true := by decide
    refine ⟨c8r456targets, c8r456choice, ?_, checked⟩
    intro S h
    simp only [c8r456targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L11_lift _ (familyLookup_sound F9B002L11 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 29 _ (by rfl)))
  have c8r457_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)] := by
    let c8r457targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2)]]
    let c8r457choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r457targets [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)] c8r457choice = true := by decide
    refine ⟨c8r457targets, c8r457choice, ?_, checked⟩
    intro S h
    simp only [c8r457targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 2 _ (by rfl)))
  have c8r458_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)] := by
    let c8r458targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)]]
    let c8r458choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r458targets [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)] c8r458choice = true := by decide
    refine ⟨c8r458targets, c8r458choice, ?_, checked⟩
    intro S h
    simp only [c8r458targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 4 _ (by rfl)))
  have c8r459_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)] := by
    let c8r459targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1)]]
    let c8r459choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r459targets [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)] c8r459choice = true := by decide
    refine ⟨c8r459targets, c8r459choice, ?_, checked⟩
    intro S h
    simp only [c8r459targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 6 _ (by rfl)))
  have c8r460_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)] := by
    let c8r460targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1)]]
    let c8r460choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r460targets [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)] c8r460choice = true := by decide
    refine ⟨c8r460targets, c8r460choice, ?_, checked⟩
    intro S h
    simp only [c8r460targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 9 _ (by rfl)))
  have c8r461_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)] := by
    let c8r461targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0)]]
    let c8r461choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r461targets [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)] c8r461choice = true := by decide
    refine ⟨c8r461targets, c8r461choice, ?_, checked⟩
    intro S h
    simp only [c8r461targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 11 _ (by rfl)))
  have c8r462_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r462targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r462choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r462targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)] c8r462choice = true := by decide
    refine ⟨c8r462targets, c8r462choice, ?_, checked⟩
    intro S h
    simp only [c8r462targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 16 _ (by rfl)))
  have c8r463_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r463targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r463choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r463targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)] c8r463choice = true := by decide
    refine ⟨c8r463targets, c8r463choice, ?_, checked⟩
    intro S h
    simp only [c8r463targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 20 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r456_closed
  · subst row; exact c8r457_closed
  · subst row; exact c8r458_closed
  · subst row; exact c8r459_closed
  · subst row; exact c8r460_closed
  · subst row; exact c8r461_closed
  · subst row; exact c8r462_closed
  · subst row; exact c8r463_closed
theorem C8R00448G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r464_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r464targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r464choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r464targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)] c8r464choice = true := by decide
    refine ⟨c8r464targets, c8r464choice, ?_, checked⟩
    intro S h
    simp only [c8r464targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 22 _ (by rfl)))
  have c8r465_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r465targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r465choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r465targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)] c8r465choice = true := by decide
    refine ⟨c8r465targets, c8r465choice, ?_, checked⟩
    intro S h
    simp only [c8r465targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 24 _ (by rfl)))
  have c8r466_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r466targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r466choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r466targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)] c8r466choice = true := by decide
    refine ⟨c8r466targets, c8r466choice, ?_, checked⟩
    intro S h
    simp only [c8r466targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 27 _ (by rfl)))
  have c8r467_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)] := by
    let c8r467targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c8r467choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r467targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)] c8r467choice = true := by decide
    refine ⟨c8r467targets, c8r467choice, ?_, checked⟩
    intro S h
    simp only [c8r467targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 30 _ (by rfl)))
  have c8r468_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)] := by
    let c8r468targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c8r468choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r468targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)] c8r468choice = true := by decide
    refine ⟨c8r468targets, c8r468choice, ?_, checked⟩
    intro S h
    simp only [c8r468targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 1 _ (by rfl)))
  have c8r469_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)] := by
    let c8r469targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c8r469choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r469targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)] c8r469choice = true := by decide
    refine ⟨c8r469targets, c8r469choice, ?_, checked⟩
    intro S h
    simp only [c8r469targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 4 _ (by rfl)))
  have c8r470_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)] := by
    let c8r470targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c8r470choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r470targets [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)] c8r470choice = true := by decide
    refine ⟨c8r470targets, c8r470choice, ?_, checked⟩
    intro S h
    simp only [c8r470targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 7 _ (by rfl)))
  have c8r471_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)] := by
    let c8r471targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c8r471choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r471targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)] c8r471choice = true := by decide
    refine ⟨c8r471targets, c8r471choice, ?_, checked⟩
    intro S h
    simp only [c8r471targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L12_lift _ (familyLookup_sound F9B002L12 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 12 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r464_closed
  · subst row; exact c8r465_closed
  · subst row; exact c8r466_closed
  · subst row; exact c8r467_closed
  · subst row; exact c8r468_closed
  · subst row; exact c8r469_closed
  · subst row; exact c8r470_closed
  · subst row; exact c8r471_closed
theorem C8R00448G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r472_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)] := by
    let c8r472targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c8r472choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r472targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)] c8r472choice = true := by decide
    refine ⟨c8r472targets, c8r472choice, ?_, checked⟩
    intro S h
    simp only [c8r472targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L41_lift _ (familyLookup_sound F9B002L41 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 14 _ (by rfl)))
  have c8r473_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)] := by
    let c8r473targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c8r473choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r473targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)] c8r473choice = true := by decide
    refine ⟨c8r473targets, c8r473choice, ?_, checked⟩
    intro S h
    simp only [c8r473targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 16 _ (by rfl)))
  have c8r474_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)] := by
    let c8r474targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c8r474choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r474targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)] c8r474choice = true := by decide
    refine ⟨c8r474targets, c8r474choice, ?_, checked⟩
    intro S h
    simp only [c8r474targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L6_lift _ (familyLookup_sound F9B002L6 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 20 _ (by rfl)))
  have c8r475_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)] := by
    let c8r475targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c8r475choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r475targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)] c8r475choice = true := by decide
    refine ⟨c8r475targets, c8r475choice, ?_, checked⟩
    intro S h
    simp only [c8r475targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 23 _ (by rfl)))
  have c8r476_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)] := by
    let c8r476targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c8r476choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r476targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)] c8r476choice = true := by decide
    refine ⟨c8r476targets, c8r476choice, ?_, checked⟩
    intro S h
    simp only [c8r476targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 25 _ (by rfl)))
  have c8r477_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)] := by
    let c8r477targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c8r477choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r477targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)] c8r477choice = true := by decide
    refine ⟨c8r477targets, c8r477choice, ?_, checked⟩
    intro S h
    simp only [c8r477targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L13_lift _ (familyLookup_sound F9B002L13 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 28 _ (by rfl)))
  have c8r478_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)] := by
    let c8r478targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c8r478choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r478targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)] c8r478choice = true := by decide
    refine ⟨c8r478targets, c8r478choice, ?_, checked⟩
    intro S h
    simp only [c8r478targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 31 _ (by rfl)))
  have c8r479_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)] := by
    let c8r479targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c8r479choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r479targets [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)] c8r479choice = true := by decide
    refine ⟨c8r479targets, c8r479choice, ?_, checked⟩
    intro S h
    simp only [c8r479targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L42_lift _ (familyLookup_sound F9B002L42 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L7_lift _ (familyLookup_sound F9B002L7 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 2 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r472_closed
  · subst row; exact c8r473_closed
  · subst row; exact c8r474_closed
  · subst row; exact c8r475_closed
  · subst row; exact c8r476_closed
  · subst row; exact c8r477_closed
  · subst row; exact c8r478_closed
  · subst row; exact c8r479_closed
theorem C8R00448_closed (row : List GridPoint) (h : FamilyMember row F8B000L14) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L14, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00448G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00448G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00448G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00448G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00448G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00448G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00448G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00448G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00448G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00448G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00448G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00448G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00448G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00448G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00448G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00448G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00448G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00448G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00448G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00448G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00448G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00448G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00448G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00448G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00448G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00448G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00448G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00448G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00448G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00448G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00448G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00448G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
