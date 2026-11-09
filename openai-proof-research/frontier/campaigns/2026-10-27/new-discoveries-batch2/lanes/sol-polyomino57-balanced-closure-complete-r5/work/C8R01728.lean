import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01728G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1728_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c8r1728targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c8r1728choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1728targets [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)] c8r1728choice = true := by decide
    refine ⟨c8r1728targets, c8r1728choice, ?_, checked⟩
    intro S h
    simp only [c8r1728targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 31 _ (by rfl)
  have c8r1729_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c8r1729targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c8r1729choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1729targets [(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)] c8r1729choice = true := by decide
    refine ⟨c8r1729targets, c8r1729choice, ?_, checked⟩
    intro S h
    simp only [c8r1729targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 3 _ (by rfl)
  have c8r1730_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r1730targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r1730choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1730targets [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)] c8r1730choice = true := by decide
    refine ⟨c8r1730targets, c8r1730choice, ?_, checked⟩
    intro S h
    simp only [c8r1730targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 11 _ (by rfl)
  have c8r1731_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r1731targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r1731choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1731targets [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)] c8r1731choice = true := by decide
    refine ⟨c8r1731targets, c8r1731choice, ?_, checked⟩
    intro S h
    simp only [c8r1731targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 14 _ (by rfl)
  have c8r1732_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r1732targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r1732choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1732targets [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)] c8r1732choice = true := by decide
    refine ⟨c8r1732targets, c8r1732choice, ?_, checked⟩
    intro S h
    simp only [c8r1732targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 16 _ (by rfl)
  have c8r1733_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)] := by
    let c8r1733targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c8r1733choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1733targets [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)] c8r1733choice = true := by decide
    refine ⟨c8r1733targets, c8r1733choice, ?_, checked⟩
    intro S h
    simp only [c8r1733targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 18 _ (by rfl)
  have c8r1734_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)] := by
    let c8r1734targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c8r1734choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1734targets [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)] c8r1734choice = true := by decide
    refine ⟨c8r1734targets, c8r1734choice, ?_, checked⟩
    intro S h
    simp only [c8r1734targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 21 _ (by rfl)
  have c8r1735_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)] := by
    let c8r1735targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c8r1735choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1735targets [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)] c8r1735choice = true := by decide
    refine ⟨c8r1735targets, c8r1735choice, ?_, checked⟩
    intro S h
    simp only [c8r1735targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1728_closed
  · subst row; exact c8r1729_closed
  · subst row; exact c8r1730_closed
  · subst row; exact c8r1731_closed
  · subst row; exact c8r1732_closed
  · subst row; exact c8r1733_closed
  · subst row; exact c8r1734_closed
  · subst row; exact c8r1735_closed
theorem C8R01728G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1736_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)] := by
    let c8r1736targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c8r1736choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1736targets [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)] c8r1736choice = true := by decide
    refine ⟨c8r1736targets, c8r1736choice, ?_, checked⟩
    intro S h
    simp only [c8r1736targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 26 _ (by rfl)
  have c8r1737_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)] := by
    let c8r1737targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c8r1737choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1737targets [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)] c8r1737choice = true := by decide
    refine ⟨c8r1737targets, c8r1737choice, ?_, checked⟩
    intro S h
    simp only [c8r1737targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 29 _ (by rfl)
  have c8r1738_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)] := by
    let c8r1738targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c8r1738choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1738targets [(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)] c8r1738choice = true := by decide
    refine ⟨c8r1738targets, c8r1738choice, ?_, checked⟩
    intro S h
    simp only [c8r1738targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 1 _ (by rfl)
  have c8r1739_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c8r1739targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c8r1739choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1739targets [(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)] c8r1739choice = true := by decide
    refine ⟨c8r1739targets, c8r1739choice, ?_, checked⟩
    intro S h
    simp only [c8r1739targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 6 _ (by rfl)
  have c8r1740_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c8r1740targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c8r1740choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1740targets [(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)] c8r1740choice = true := by decide
    refine ⟨c8r1740targets, c8r1740choice, ?_, checked⟩
    intro S h
    simp only [c8r1740targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 8 _ (by rfl)
  have c8r1741_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c8r1741targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c8r1741choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1741targets [(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)] c8r1741choice = true := by decide
    refine ⟨c8r1741targets, c8r1741choice, ?_, checked⟩
    intro S h
    simp only [c8r1741targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 10 _ (by rfl)
  have c8r1742_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c8r1742targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c8r1742choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1742targets [(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)] c8r1742choice = true := by decide
    refine ⟨c8r1742targets, c8r1742choice, ?_, checked⟩
    intro S h
    simp only [c8r1742targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 14 _ (by rfl)
  have c8r1743_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c8r1743targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1743choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1743targets [(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)] c8r1743choice = true := by decide
    refine ⟨c8r1743targets, c8r1743choice, ?_, checked⟩
    intro S h
    simp only [c8r1743targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1736_closed
  · subst row; exact c8r1737_closed
  · subst row; exact c8r1738_closed
  · subst row; exact c8r1739_closed
  · subst row; exact c8r1740_closed
  · subst row; exact c8r1741_closed
  · subst row; exact c8r1742_closed
  · subst row; exact c8r1743_closed
theorem C8R01728G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1744_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r1744targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r1744choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1744targets [(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)] c8r1744choice = true := by decide
    refine ⟨c8r1744targets, c8r1744choice, ?_, checked⟩
    intro S h
    simp only [c8r1744targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 27 _ (by rfl)
  have c8r1745_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r1745targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r1745choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1745targets [(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)] c8r1745choice = true := by decide
    refine ⟨c8r1745targets, c8r1745choice, ?_, checked⟩
    intro S h
    simp only [c8r1745targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 30 _ (by rfl)
  have c8r1746_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r1746targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r1746choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1746targets [(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)] c8r1746choice = true := by decide
    refine ⟨c8r1746targets, c8r1746choice, ?_, checked⟩
    intro S h
    simp only [c8r1746targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 0 _ (by rfl)
  have c8r1747_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c8r1747targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c8r1747choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1747targets [(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)] c8r1747choice = true := by decide
    refine ⟨c8r1747targets, c8r1747choice, ?_, checked⟩
    intro S h
    simp only [c8r1747targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 2 _ (by rfl)
  have c8r1748_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)] := by
    let c8r1748targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c8r1748choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,1),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1748targets [(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)] c8r1748choice = true := by decide
    refine ⟨c8r1748targets, c8r1748choice, ?_, checked⟩
    intro S h
    simp only [c8r1748targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 7 _ (by rfl)
  have c8r1749_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)] := by
    let c8r1749targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c8r1749choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,1),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1749targets [(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)] c8r1749choice = true := by decide
    refine ⟨c8r1749targets, c8r1749choice, ?_, checked⟩
    intro S h
    simp only [c8r1749targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 13 _ (by rfl)
  have c8r1750_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1750targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1750choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1750targets [(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)] c8r1750choice = true := by decide
    refine ⟨c8r1750targets, c8r1750choice, ?_, checked⟩
    intro S h
    simp only [c8r1750targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 21 _ (by rfl)
  have c8r1751_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r1751targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r1751choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,5),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1751targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)] c8r1751choice = true := by decide
    refine ⟨c8r1751targets, c8r1751choice, ?_, checked⟩
    intro S h
    simp only [c8r1751targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1744_closed
  · subst row; exact c8r1745_closed
  · subst row; exact c8r1746_closed
  · subst row; exact c8r1747_closed
  · subst row; exact c8r1748_closed
  · subst row; exact c8r1749_closed
  · subst row; exact c8r1750_closed
  · subst row; exact c8r1751_closed
theorem C8R01728G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1752_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c8r1752targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c8r1752choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1752targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)] c8r1752choice = true := by decide
    refine ⟨c8r1752targets, c8r1752choice, ?_, checked⟩
    intro S h
    simp only [c8r1752targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 0 _ (by rfl)
  have c8r1753_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r1753targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r1753choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1753targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] c8r1753choice = true := by decide
    refine ⟨c8r1753targets, c8r1753choice, ?_, checked⟩
    intro S h
    simp only [c8r1753targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 3 _ (by rfl)
  have c8r1754_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r1754targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r1754choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1754targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] c8r1754choice = true := by decide
    refine ⟨c8r1754targets, c8r1754choice, ?_, checked⟩
    intro S h
    simp only [c8r1754targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 5 _ (by rfl)
  have c8r1755_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r1755targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r1755choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1755targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] c8r1755choice = true := by decide
    refine ⟨c8r1755targets, c8r1755choice, ?_, checked⟩
    intro S h
    simp only [c8r1755targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 7 _ (by rfl)
  have c8r1756_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c8r1756targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c8r1756choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1756targets [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)] c8r1756choice = true := by decide
    refine ⟨c8r1756targets, c8r1756choice, ?_, checked⟩
    intro S h
    simp only [c8r1756targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 13 _ (by rfl)
  have c8r1757_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r1757targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r1757choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1757targets [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] c8r1757choice = true := by decide
    refine ⟨c8r1757targets, c8r1757choice, ?_, checked⟩
    intro S h
    simp only [c8r1757targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 22 _ (by rfl)
  have c8r1758_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c8r1758targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c8r1758choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,6),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0))),((3,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1758targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] c8r1758choice = true := by decide
    refine ⟨c8r1758targets, c8r1758choice, ?_, checked⟩
    intro S h
    simp only [c8r1758targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 31 _ (by rfl)
  have c8r1759_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] := by
    let c8r1759targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)]]
    let c8r1759choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,5),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1759targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] c8r1759choice = true := by decide
    refine ⟨c8r1759targets, c8r1759choice, ?_, checked⟩
    intro S h
    simp only [c8r1759targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,true,true] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1752_closed
  · subst row; exact c8r1753_closed
  · subst row; exact c8r1754_closed
  · subst row; exact c8r1755_closed
  · subst row; exact c8r1756_closed
  · subst row; exact c8r1757_closed
  · subst row; exact c8r1758_closed
  · subst row; exact c8r1759_closed
theorem C8R01728_closed (row : List GridPoint) (h : FamilyMember row F8B000L54) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L54, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01728G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01728G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01728G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01728G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01728G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01728G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01728G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01728G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01728G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01728G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01728G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01728G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01728G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01728G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01728G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01728G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01728G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01728G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01728G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01728G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01728G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01728G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01728G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01728G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01728G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01728G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01728G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01728G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01728G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01728G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01728G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01728G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
