import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00672G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r672_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r672targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r672choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r672targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] c8r672choice = true := by decide
    refine ⟨c8r672targets, c8r672choice, ?_, checked⟩
    intro S h
    simp only [c8r672targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 28 _ (by rfl)))
  have c8r673_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r673targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r673choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r673targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] c8r673choice = true := by decide
    refine ⟨c8r673targets, c8r673choice, ?_, checked⟩
    intro S h
    simp only [c8r673targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 30 _ (by rfl)))
  have c8r674_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)] := by
    let c8r674targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c8r674choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r674targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)] c8r674choice = true := by decide
    refine ⟨c8r674targets, c8r674choice, ?_, checked⟩
    intro S h
    simp only [c8r674targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 0 _ (by rfl)))
  have c8r675_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)] := by
    let c8r675targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c8r675choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r675targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)] c8r675choice = true := by decide
    refine ⟨c8r675targets, c8r675choice, ?_, checked⟩
    intro S h
    simp only [c8r675targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 3 _ (by rfl)))
  have c8r676_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)] := by
    let c8r676targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c8r676choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r676targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)] c8r676choice = true := by decide
    refine ⟨c8r676targets, c8r676choice, ?_, checked⟩
    intro S h
    simp only [c8r676targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 5 _ (by rfl)))
  have c8r677_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)] := by
    let c8r677targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c8r677choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r677targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)] c8r677choice = true := by decide
    refine ⟨c8r677targets, c8r677choice, ?_, checked⟩
    intro S h
    simp only [c8r677targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 8 _ (by rfl)))
  have c8r678_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)] := by
    let c8r678targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c8r678choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r678targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)] c8r678choice = true := by decide
    refine ⟨c8r678targets, c8r678choice, ?_, checked⟩
    intro S h
    simp only [c8r678targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 11 _ (by rfl)))
  have c8r679_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)] := by
    let c8r679targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c8r679choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,5),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r679targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)] c8r679choice = true := by decide
    refine ⟨c8r679targets, c8r679choice, ?_, checked⟩
    intro S h
    simp only [c8r679targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 16 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r672_closed
  · subst row; exact c8r673_closed
  · subst row; exact c8r674_closed
  · subst row; exact c8r675_closed
  · subst row; exact c8r676_closed
  · subst row; exact c8r677_closed
  · subst row; exact c8r678_closed
  · subst row; exact c8r679_closed
theorem C8R00672G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r680_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)] := by
    let c8r680targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c8r680choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r680targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)] c8r680choice = true := by decide
    refine ⟨c8r680targets, c8r680choice, ?_, checked⟩
    intro S h
    simp only [c8r680targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 20 _ (by rfl)))
  have c8r681_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)] := by
    let c8r681targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c8r681choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r681targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)] c8r681choice = true := by decide
    refine ⟨c8r681targets, c8r681choice, ?_, checked⟩
    intro S h
    simp only [c8r681targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 22 _ (by rfl)))
  have c8r682_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)] := by
    let c8r682targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c8r682choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r682targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)] c8r682choice = true := by decide
    refine ⟨c8r682targets, c8r682choice, ?_, checked⟩
    intro S h
    simp only [c8r682targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 24 _ (by rfl)))
  have c8r683_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)] := by
    let c8r683targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c8r683choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r683targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)] c8r683choice = true := by decide
    refine ⟨c8r683targets, c8r683choice, ?_, checked⟩
    intro S h
    simp only [c8r683targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 27 _ (by rfl)))
  have c8r684_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)] := by
    let c8r684targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c8r684choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r684targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)] c8r684choice = true := by decide
    refine ⟨c8r684targets, c8r684choice, ?_, checked⟩
    intro S h
    simp only [c8r684targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 30 _ (by rfl)))
  have c8r685_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)] := by
    let c8r685targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c8r685choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r685targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)] c8r685choice = true := by decide
    refine ⟨c8r685targets, c8r685choice, ?_, checked⟩
    intro S h
    simp only [c8r685targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 1 _ (by rfl)))
  have c8r686_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)] := by
    let c8r686targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c8r686choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r686targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)] c8r686choice = true := by decide
    refine ⟨c8r686targets, c8r686choice, ?_, checked⟩
    intro S h
    simp only [c8r686targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 4 _ (by rfl)))
  have c8r687_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)] := by
    let c8r687targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c8r687choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r687targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)] c8r687choice = true := by decide
    refine ⟨c8r687targets, c8r687choice, ?_, checked⟩
    intro S h
    simp only [c8r687targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 7 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r680_closed
  · subst row; exact c8r681_closed
  · subst row; exact c8r682_closed
  · subst row; exact c8r683_closed
  · subst row; exact c8r684_closed
  · subst row; exact c8r685_closed
  · subst row; exact c8r686_closed
  · subst row; exact c8r687_closed
theorem C8R00672G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r688_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c8r688targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c8r688choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r688targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)] c8r688choice = true := by decide
    refine ⟨c8r688targets, c8r688choice, ?_, checked⟩
    intro S h
    simp only [c8r688targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 12 _ (by rfl)))
  have c8r689_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c8r689targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c8r689choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r689targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] c8r689choice = true := by decide
    refine ⟨c8r689targets, c8r689choice, ?_, checked⟩
    intro S h
    simp only [c8r689targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 14 _ (by rfl)))
  have c8r690_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c8r690targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c8r690choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r690targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] c8r690choice = true := by decide
    refine ⟨c8r690targets, c8r690choice, ?_, checked⟩
    intro S h
    simp only [c8r690targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 16 _ (by rfl)))
  have c8r691_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c8r691targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c8r691choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,4),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r691targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)] c8r691choice = true := by decide
    refine ⟨c8r691targets, c8r691choice, ?_, checked⟩
    intro S h
    simp only [c8r691targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 20 _ (by rfl)))
  have c8r692_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)] := by
    let c8r692targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c8r692choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r692targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)] c8r692choice = true := by decide
    refine ⟨c8r692targets, c8r692choice, ?_, checked⟩
    intro S h
    simp only [c8r692targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 23 _ (by rfl)))
  have c8r693_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)] := by
    let c8r693targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c8r693choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r693targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)] c8r693choice = true := by decide
    refine ⟨c8r693targets, c8r693choice, ?_, checked⟩
    intro S h
    simp only [c8r693targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 25 _ (by rfl)))
  have c8r694_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c8r694targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c8r694choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r694targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)] c8r694choice = true := by decide
    refine ⟨c8r694targets, c8r694choice, ?_, checked⟩
    intro S h
    simp only [c8r694targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 28 _ (by rfl)))
  have c8r695_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)] := by
    let c8r695targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c8r695choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r695targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)] c8r695choice = true := by decide
    refine ⟨c8r695targets, c8r695choice, ?_, checked⟩
    intro S h
    simp only [c8r695targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 31 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r688_closed
  · subst row; exact c8r689_closed
  · subst row; exact c8r690_closed
  · subst row; exact c8r691_closed
  · subst row; exact c8r692_closed
  · subst row; exact c8r693_closed
  · subst row; exact c8r694_closed
  · subst row; exact c8r695_closed
theorem C8R00672G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r696_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)] := by
    let c8r696targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c8r696choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,2),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r696targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)] c8r696choice = true := by decide
    refine ⟨c8r696targets, c8r696choice, ?_, checked⟩
    intro S h
    simp only [c8r696targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L32_lift _ (familyLookup_sound F9B000L32 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L6_lift _ (familyLookup_sound F9B001L6 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L7_lift _ (familyLookup_sound F9B001L7 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 2 _ (by rfl)))
  have c8r697_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)] := by
    let c8r697targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,4),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,5),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,0),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2)],[(0,1),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2)]]
    let c8r697choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((-1,5),(4,(1,0))),((0,-1),(5,(0,1))),((0,1),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((1,5),(11,(0,0))),((2,0),(12,(0,0))),((2,1),(13,(0,0))),((2,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r697targets [(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)] c8r697choice = true := by decide
    refine ⟨c8r697targets, c8r697choice, ?_, checked⟩
    intro S h
    simp only [c8r697targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 25 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 7 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 28 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 9 _ (by rfl)))
  have c8r698_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)] := by
    let c8r698targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)]]
    let c8r698choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,1),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r698targets [(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)] c8r698choice = true := by decide
    refine ⟨c8r698targets, c8r698choice, ?_, checked⟩
    intro S h
    simp only [c8r698targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 26 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 8 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 14 _ (by rfl)))
  have c8r699_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)] := by
    let c8r699targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4)]]
    let c8r699choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,1),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,3),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r699targets [(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)] c8r699choice = true := by decide
    refine ⟨c8r699targets, c8r699choice, ?_, checked⟩
    intro S h
    simp only [c8r699targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 27 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 9 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 19 _ (by rfl)))
  have c8r700_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)] := by
    let c8r700targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0)],[(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0)]]
    let c8r700choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,1),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((3,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r700targets [(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)] c8r700choice = true := by decide
    refine ⟨c8r700targets, c8r700choice, ?_, checked⟩
    intro S h
    simp only [c8r700targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 28 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 10 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 22 _ (by rfl)))
  have c8r701_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)] := by
    let c8r701targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1)]]
    let c8r701choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,1),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r701targets [(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)] c8r701choice = true := by decide
    refine ⟨c8r701targets, c8r701choice, ?_, checked⟩
    intro S h
    simp only [c8r701targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 29 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 11 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 24 _ (by rfl)))
  have c8r702_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)] := by
    let c8r702targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2)]]
    let c8r702choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,1),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r702targets [(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)] c8r702choice = true := by decide
    refine ⟨c8r702targets, c8r702choice, ?_, checked⟩
    intro S h
    simp only [c8r702targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 30 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 12 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L42_lift _ (familyLookup_sound F9B004L42 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 26 _ (by rfl)))
  have c8r703_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r703targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r703choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r703targets [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)] c8r703choice = true := by decide
    refine ⟨c8r703targets, c8r703choice, ?_, checked⟩
    intro S h
    simp only [c8r703targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L40_lift _ (familyLookup_sound F9B003L40 [] 31 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L18_lift _ (familyLookup_sound F9B004L18 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L39_lift _ (familyLookup_sound F9B000L39 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L21_lift _ (familyLookup_sound F9B002L21 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L8_lift _ (familyLookup_sound F9B001L8 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L9_lift _ (familyLookup_sound F9B001L9 [] 1 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r696_closed
  · subst row; exact c8r697_closed
  · subst row; exact c8r698_closed
  · subst row; exact c8r699_closed
  · subst row; exact c8r700_closed
  · subst row; exact c8r701_closed
  · subst row; exact c8r702_closed
  · subst row; exact c8r703_closed
theorem C8R00672_closed (row : List GridPoint) (h : FamilyMember row F8B000L21) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L21, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00672G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00672G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00672G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00672G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00672G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00672G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00672G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00672G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00672G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00672G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00672G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00672G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00672G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00672G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00672G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00672G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00672G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00672G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00672G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00672G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00672G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00672G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00672G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00672G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00672G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00672G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00672G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00672G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00672G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00672G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00672G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00672G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
