import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01664G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1664_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)] := by
    let c8r1664targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c8r1664choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,4),(10,(0,0))),((5,2),(11,(0,0))),((5,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1664targets [(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)] c8r1664choice = true := by decide
    refine ⟨c8r1664targets, c8r1664choice, ?_, checked⟩
    intro S h
    simp only [c8r1664targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 1 _ (by rfl)
  have c8r1665_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)] := by
    let c8r1665targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c8r1665choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,3),(12,(0,0))),((6,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1665targets [(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)] c8r1665choice = true := by decide
    refine ⟨c8r1665targets, c8r1665choice, ?_, checked⟩
    intro S h
    simp only [c8r1665targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 4 _ (by rfl)
  have c8r1666_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c8r1666targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c8r1666choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1666targets [(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)] c8r1666choice = true := by decide
    refine ⟨c8r1666targets, c8r1666choice, ?_, checked⟩
    intro S h
    simp only [c8r1666targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 9 _ (by rfl)
  have c8r1667_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c8r1667targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c8r1667choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1667targets [(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] c8r1667choice = true := by decide
    refine ⟨c8r1667targets, c8r1667choice, ?_, checked⟩
    intro S h
    simp only [c8r1667targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 11 _ (by rfl)
  have c8r1668_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c8r1668targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c8r1668choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1668targets [(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] c8r1668choice = true := by decide
    refine ⟨c8r1668targets, c8r1668choice, ?_, checked⟩
    intro S h
    simp only [c8r1668targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 13 _ (by rfl)
  have c8r1669_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c8r1669targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c8r1669choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,4),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1669targets [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)] c8r1669choice = true := by decide
    refine ⟨c8r1669targets, c8r1669choice, ?_, checked⟩
    intro S h
    simp only [c8r1669targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 17 _ (by rfl)
  have c8r1670_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)] := by
    let c8r1670targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c8r1670choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1670targets [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)] c8r1670choice = true := by decide
    refine ⟨c8r1670targets, c8r1670choice, ?_, checked⟩
    intro S h
    simp only [c8r1670targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 20 _ (by rfl)
  have c8r1671_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)] := by
    let c8r1671targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c8r1671choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,3),(12,(0,0))),((6,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1671targets [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)] c8r1671choice = true := by decide
    refine ⟨c8r1671targets, c8r1671choice, ?_, checked⟩
    intro S h
    simp only [c8r1671targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 22 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1664_closed
  · subst row; exact c8r1665_closed
  · subst row; exact c8r1666_closed
  · subst row; exact c8r1667_closed
  · subst row; exact c8r1668_closed
  · subst row; exact c8r1669_closed
  · subst row; exact c8r1670_closed
  · subst row; exact c8r1671_closed
theorem C8R01664G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1672_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c8r1672targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c8r1672choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1672targets [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)] c8r1672choice = true := by decide
    refine ⟨c8r1672targets, c8r1672choice, ?_, checked⟩
    intro S h
    simp only [c8r1672targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 25 _ (by rfl)
  have c8r1673_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)] := by
    let c8r1673targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c8r1673choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,3),(12,(0,0))),((6,1),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1673targets [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)] c8r1673choice = true := by decide
    refine ⟨c8r1673targets, c8r1673choice, ?_, checked⟩
    intro S h
    simp only [c8r1673targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 28 _ (by rfl)
  have c8r1674_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)] := by
    let c8r1674targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c8r1674choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,2),(14,(0,0))),((7,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1674targets [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)] c8r1674choice = true := by decide
    refine ⟨c8r1674targets, c8r1674choice, ?_, checked⟩
    intro S h
    simp only [c8r1674targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 31 _ (by rfl)
  have c8r1675_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)] := by
    let c8r1675targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)]]
    let c8r1675choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((0,5),(5,(0,0))),((1,0),(6,(0,0))),((1,6),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((2,5),(12,(0,0))),((3,0),(13,(0,0))),((3,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1675targets [(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)] c8r1675choice = true := by decide
    refine ⟨c8r1675targets, c8r1675choice, ?_, checked⟩
    intro S h
    simp only [c8r1675targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 6 _ (by rfl)
  have c8r1676_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c8r1676targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1676choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1676targets [(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c8r1676choice = true := by decide
    refine ⟨c8r1676targets, c8r1676choice, ?_, checked⟩
    intro S h
    simp only [c8r1676targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 12 _ (by rfl)
  have c8r1677_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)] := by
    let c8r1677targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)]]
    let c8r1677choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1677targets [(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)] c8r1677choice = true := by decide
    refine ⟨c8r1677targets, c8r1677choice, ?_, checked⟩
    intro S h
    simp only [c8r1677targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 16 _ (by rfl)
  have c8r1678_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)] := by
    let c8r1678targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)]]
    let c8r1678choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,5),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1678targets [(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)] c8r1678choice = true := by decide
    refine ⟨c8r1678targets, c8r1678choice, ?_, checked⟩
    intro S h
    simp only [c8r1678targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 20 _ (by rfl)
  have c8r1679_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] := by
    let c8r1679targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)]]
    let c8r1679choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1679targets [(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] c8r1679choice = true := by decide
    refine ⟨c8r1679targets, c8r1679choice, ?_, checked⟩
    intro S h
    simp only [c8r1679targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 22 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1672_closed
  · subst row; exact c8r1673_closed
  · subst row; exact c8r1674_closed
  · subst row; exact c8r1675_closed
  · subst row; exact c8r1676_closed
  · subst row; exact c8r1677_closed
  · subst row; exact c8r1678_closed
  · subst row; exact c8r1679_closed
theorem C8R01664G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1680_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] := by
    let c8r1680targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)]]
    let c8r1680choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1680targets [(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] c8r1680choice = true := by decide
    refine ⟨c8r1680targets, c8r1680choice, ?_, checked⟩
    intro S h
    simp only [c8r1680targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 24 _ (by rfl)
  have c8r1681_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] := by
    let c8r1681targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1681choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,-1),(11,(0,1))),((3,2),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1681targets [(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] c8r1681choice = true := by decide
    refine ⟨c8r1681targets, c8r1681choice, ?_, checked⟩
    intro S h
    simp only [c8r1681targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 30 _ (by rfl)
  have c8r1682_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1682targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1682choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1682targets [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] c8r1682choice = true := by decide
    refine ⟨c8r1682targets, c8r1682choice, ?_, checked⟩
    intro S h
    simp only [c8r1682targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 5 _ (by rfl)
  have c8r1683_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r1683targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r1683choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1683targets [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] c8r1683choice = true := by decide
    refine ⟨c8r1683targets, c8r1683choice, ?_, checked⟩
    intro S h
    simp only [c8r1683targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 8 _ (by rfl)
  have c8r1684_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r1684targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r1684choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1684targets [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] c8r1684choice = true := by decide
    refine ⟨c8r1684targets, c8r1684choice, ?_, checked⟩
    intro S h
    simp only [c8r1684targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 10 _ (by rfl)
  have c8r1685_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r1685targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r1685choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1685targets [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] c8r1685choice = true := by decide
    refine ⟨c8r1685targets, c8r1685choice, ?_, checked⟩
    intro S h
    simp only [c8r1685targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 12 _ (by rfl)
  have c8r1686_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)] := by
    let c8r1686targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)]]
    let c8r1686choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,5),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1686targets [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)] c8r1686choice = true := by decide
    refine ⟨c8r1686targets, c8r1686choice, ?_, checked⟩
    intro S h
    simp only [c8r1686targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 17 _ (by rfl)
  have c8r1687_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)] := by
    let c8r1687targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)]]
    let c8r1687choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1687targets [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)] c8r1687choice = true := by decide
    refine ⟨c8r1687targets, c8r1687choice, ?_, checked⟩
    intro S h
    simp only [c8r1687targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1680_closed
  · subst row; exact c8r1681_closed
  · subst row; exact c8r1682_closed
  · subst row; exact c8r1683_closed
  · subst row; exact c8r1684_closed
  · subst row; exact c8r1685_closed
  · subst row; exact c8r1686_closed
  · subst row; exact c8r1687_closed
theorem C8R01664G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1688_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)] := by
    let c8r1688targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)]]
    let c8r1688choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1688targets [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)] c8r1688choice = true := by decide
    refine ⟨c8r1688targets, c8r1688choice, ?_, checked⟩
    intro S h
    simp only [c8r1688targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 23 _ (by rfl)
  have c8r1689_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)] := by
    let c8r1689targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)]]
    let c8r1689choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1689targets [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)] c8r1689choice = true := by decide
    refine ⟨c8r1689targets, c8r1689choice, ?_, checked⟩
    intro S h
    simp only [c8r1689targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 26 _ (by rfl)
  have c8r1690_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)] := by
    let c8r1690targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1690choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1690targets [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)] c8r1690choice = true := by decide
    refine ⟨c8r1690targets, c8r1690choice, ?_, checked⟩
    intro S h
    simp only [c8r1690targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 29 _ (by rfl)
  have c8r1691_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)] := by
    let c8r1691targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c8r1691choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1691targets [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)] c8r1691choice = true := by decide
    refine ⟨c8r1691targets, c8r1691choice, ?_, checked⟩
    intro S h
    simp only [c8r1691targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 31 _ (by rfl)
  have c8r1692_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)] := by
    let c8r1692targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c8r1692choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1692targets [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)] c8r1692choice = true := by decide
    refine ⟨c8r1692targets, c8r1692choice, ?_, checked⟩
    intro S h
    simp only [c8r1692targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 2 _ (by rfl)
  have c8r1693_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)] := by
    let c8r1693targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c8r1693choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1693targets [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)] c8r1693choice = true := by decide
    refine ⟨c8r1693targets, c8r1693choice, ?_, checked⟩
    intro S h
    simp only [c8r1693targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 5 _ (by rfl)
  have c8r1694_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r1694targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r1694choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1694targets [(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)] c8r1694choice = true := by decide
    refine ⟨c8r1694targets, c8r1694choice, ?_, checked⟩
    intro S h
    simp only [c8r1694targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 10 _ (by rfl)
  have c8r1695_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)] := by
    let c8r1695targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,1)]]
    let c8r1695choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1695targets [(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)] c8r1695choice = true := by decide
    refine ⟨c8r1695targets, c8r1695choice, ?_, checked⟩
    intro S h
    simp only [c8r1695targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1688_closed
  · subst row; exact c8r1689_closed
  · subst row; exact c8r1690_closed
  · subst row; exact c8r1691_closed
  · subst row; exact c8r1692_closed
  · subst row; exact c8r1693_closed
  · subst row; exact c8r1694_closed
  · subst row; exact c8r1695_closed
theorem C8R01664_closed (row : List GridPoint) (h : FamilyMember row F8B000L52) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L52, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01664G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01664G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01664G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01664G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01664G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01664G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01664G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01664G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01664G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01664G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01664G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01664G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01664G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01664G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01664G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01664G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01664G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01664G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01664G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01664G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01664G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01664G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01664G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01664G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01664G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01664G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01664G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01664G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01664G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01664G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01664G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01664G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
