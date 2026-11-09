import F9All
import F8B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R02176G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2176_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c8r2176targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c8r2176choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2176targets [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)] c8r2176choice = true := by decide
    refine ⟨c8r2176targets, c8r2176choice, ?_, checked⟩
    intro S h
    simp only [c8r2176targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 5 _ (by rfl)
  have c8r2177_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c8r2177targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c8r2177choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2177targets [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)] c8r2177choice = true := by decide
    refine ⟨c8r2177targets, c8r2177choice, ?_, checked⟩
    intro S h
    simp only [c8r2177targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 8 _ (by rfl)
  have c8r2178_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c8r2178targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c8r2178choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2178targets [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)] c8r2178choice = true := by decide
    refine ⟨c8r2178targets, c8r2178choice, ?_, checked⟩
    intro S h
    simp only [c8r2178targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 11 _ (by rfl)
  have c8r2179_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c8r2179targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c8r2179choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2179targets [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)] c8r2179choice = true := by decide
    refine ⟨c8r2179targets, c8r2179choice, ?_, checked⟩
    intro S h
    simp only [c8r2179targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 14 _ (by rfl)
  have c8r2180_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)] := by
    let c8r2180targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c8r2180choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2180targets [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)] c8r2180choice = true := by decide
    refine ⟨c8r2180targets, c8r2180choice, ?_, checked⟩
    intro S h
    simp only [c8r2180targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 17 _ (by rfl)
  have c8r2181_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r2181targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r2181choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2181targets [(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)] c8r2181choice = true := by decide
    refine ⟨c8r2181targets, c8r2181choice, ?_, checked⟩
    intro S h
    simp only [c8r2181targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 22 _ (by rfl)
  have c8r2182_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)] := by
    let c8r2182targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)]]
    let c8r2182choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((0,4),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,6),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((2,5),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2182targets [(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)] c8r2182choice = true := by decide
    refine ⟨c8r2182targets, c8r2182choice, ?_, checked⟩
    intro S h
    simp only [c8r2182targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 29 _ (by rfl)
  have c8r2183_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c8r2183targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c8r2183choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,5),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2183targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c8r2183choice = true := by decide
    refine ⟨c8r2183targets, c8r2183choice, ?_, checked⟩
    intro S h
    simp only [c8r2183targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 3 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2176_closed
  · subst row; exact c8r2177_closed
  · subst row; exact c8r2178_closed
  · subst row; exact c8r2179_closed
  · subst row; exact c8r2180_closed
  · subst row; exact c8r2181_closed
  · subst row; exact c8r2182_closed
  · subst row; exact c8r2183_closed
theorem C8R02176G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2184_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)] := by
    let c8r2184targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)]]
    let c8r2184choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,5),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2184targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)] c8r2184choice = true := by decide
    refine ⟨c8r2184targets, c8r2184choice, ?_, checked⟩
    intro S h
    simp only [c8r2184targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 7 _ (by rfl)
  have c8r2185_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)] := by
    let c8r2185targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)]]
    let c8r2185choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,5),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2185targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)] c8r2185choice = true := by decide
    refine ⟨c8r2185targets, c8r2185choice, ?_, checked⟩
    intro S h
    simp only [c8r2185targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 11 _ (by rfl)
  have c8r2186_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] := by
    let c8r2186targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)]]
    let c8r2186choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,5),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2186targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] c8r2186choice = true := by decide
    refine ⟨c8r2186targets, c8r2186choice, ?_, checked⟩
    intro S h
    simp only [c8r2186targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 13 _ (by rfl)
  have c8r2187_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] := by
    let c8r2187targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)]]
    let c8r2187choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,5),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2187targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] c8r2187choice = true := by decide
    refine ⟨c8r2187targets, c8r2187choice, ?_, checked⟩
    intro S h
    simp only [c8r2187targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 15 _ (by rfl)
  have c8r2188_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] := by
    let c8r2188targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)]]
    let c8r2188choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,5),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2188targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] c8r2188choice = true := by decide
    refine ⟨c8r2188targets, c8r2188choice, ?_, checked⟩
    intro S h
    simp only [c8r2188targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 21 _ (by rfl)
  have c8r2189_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r2189targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r2189choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,-1),(5,(0,1))),((2,4),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2189targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] c8r2189choice = true := by decide
    refine ⟨c8r2189targets, c8r2189choice, ?_, checked⟩
    intro S h
    simp only [c8r2189targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 28 _ (by rfl)
  have c8r2190_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r2190targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r2190choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2190targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] c8r2190choice = true := by decide
    refine ⟨c8r2190targets, c8r2190choice, ?_, checked⟩
    intro S h
    simp only [c8r2190targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 31 _ (by rfl)
  have c8r2191_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r2191targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r2191choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,1),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2191targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] c8r2191choice = true := by decide
    refine ⟨c8r2191targets, c8r2191choice, ?_, checked⟩
    intro S h
    simp only [c8r2191targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2184_closed
  · subst row; exact c8r2185_closed
  · subst row; exact c8r2186_closed
  · subst row; exact c8r2187_closed
  · subst row; exact c8r2188_closed
  · subst row; exact c8r2189_closed
  · subst row; exact c8r2190_closed
  · subst row; exact c8r2191_closed
theorem C8R02176G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2192_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r2192targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r2192choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2192targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] c8r2192choice = true := by decide
    refine ⟨c8r2192targets, c8r2192choice, ?_, checked⟩
    intro S h
    simp only [c8r2192targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 3 _ (by rfl)
  have c8r2193_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)] := by
    let c8r2193targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)]]
    let c8r2193choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,5),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2193targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)] c8r2193choice = true := by decide
    refine ⟨c8r2193targets, c8r2193choice, ?_, checked⟩
    intro S h
    simp only [c8r2193targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 8 _ (by rfl)
  have c8r2194_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)] := by
    let c8r2194targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)]]
    let c8r2194choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2194targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)] c8r2194choice = true := by decide
    refine ⟨c8r2194targets, c8r2194choice, ?_, checked⟩
    intro S h
    simp only [c8r2194targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 11 _ (by rfl)
  have c8r2195_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)] := by
    let c8r2195targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)]]
    let c8r2195choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2195targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)] c8r2195choice = true := by decide
    refine ⟨c8r2195targets, c8r2195choice, ?_, checked⟩
    intro S h
    simp only [c8r2195targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 14 _ (by rfl)
  have c8r2196_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)] := by
    let c8r2196targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)]]
    let c8r2196choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2196targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)] c8r2196choice = true := by decide
    refine ⟨c8r2196targets, c8r2196choice, ?_, checked⟩
    intro S h
    simp only [c8r2196targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 17 _ (by rfl)
  have c8r2197_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)] := by
    let c8r2197targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c8r2197choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2197targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)] c8r2197choice = true := by decide
    refine ⟨c8r2197targets, c8r2197choice, ?_, checked⟩
    intro S h
    simp only [c8r2197targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 20 _ (by rfl)
  have c8r2198_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)] := by
    let c8r2198targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c8r2198choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2198targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)] c8r2198choice = true := by decide
    refine ⟨c8r2198targets, c8r2198choice, ?_, checked⟩
    intro S h
    simp only [c8r2198targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 22 _ (by rfl)
  have c8r2199_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)] := by
    let c8r2199targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c8r2199choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2199targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)] c8r2199choice = true := by decide
    refine ⟨c8r2199targets, c8r2199choice, ?_, checked⟩
    intro S h
    simp only [c8r2199targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 25 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2192_closed
  · subst row; exact c8r2193_closed
  · subst row; exact c8r2194_closed
  · subst row; exact c8r2195_closed
  · subst row; exact c8r2196_closed
  · subst row; exact c8r2197_closed
  · subst row; exact c8r2198_closed
  · subst row; exact c8r2199_closed
theorem C8R02176G3 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2200_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)] := by
    let c8r2200targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c8r2200choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2200targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)] c8r2200choice = true := by decide
    refine ⟨c8r2200targets, c8r2200choice, ?_, checked⟩
    intro S h
    simp only [c8r2200targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 28 _ (by rfl)
  have c8r2201_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r2201targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r2201choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2201targets [(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)] c8r2201choice = true := by decide
    refine ⟨c8r2201targets, c8r2201choice, ?_, checked⟩
    intro S h
    simp only [c8r2201targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 1 _ (by rfl)
  have c8r2202_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)] := by
    let c8r2202targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,1)]]
    let c8r2202choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2202targets [(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)] c8r2202choice = true := by decide
    refine ⟨c8r2202targets, c8r2202choice, ?_, checked⟩
    intro S h
    simp only [c8r2202targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 7 _ (by rfl)
  have c8r2203_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)] := by
    let c8r2203targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c8r2203choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2203targets [(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)] c8r2203choice = true := by decide
    refine ⟨c8r2203targets, c8r2203choice, ?_, checked⟩
    intro S h
    simp only [c8r2203targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 12 _ (by rfl)
  have c8r2204_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)] := by
    let c8r2204targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c8r2204choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2204targets [(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)] c8r2204choice = true := by decide
    refine ⟨c8r2204targets, c8r2204choice, ?_, checked⟩
    intro S h
    simp only [c8r2204targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 14 _ (by rfl)
  have c8r2205_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)] := by
    let c8r2205targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c8r2205choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2205targets [(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)] c8r2205choice = true := by decide
    refine ⟨c8r2205targets, c8r2205choice, ?_, checked⟩
    intro S h
    simp only [c8r2205targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 16 _ (by rfl)
  have c8r2206_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)] := by
    let c8r2206targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c8r2206choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2206targets [(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)] c8r2206choice = true := by decide
    refine ⟨c8r2206targets, c8r2206choice, ?_, checked⟩
    intro S h
    simp only [c8r2206targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 20 _ (by rfl)
  have c8r2207_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r2207targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r2207choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,4),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2207targets [(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)] c8r2207choice = true := by decide
    refine ⟨c8r2207targets, c8r2207choice, ?_, checked⟩
    intro S h
    simp only [c8r2207targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,false,true,true,false,true] 26 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2200_closed
  · subst row; exact c8r2201_closed
  · subst row; exact c8r2202_closed
  · subst row; exact c8r2203_closed
  · subst row; exact c8r2204_closed
  · subst row; exact c8r2205_closed
  · subst row; exact c8r2206_closed
  · subst row; exact c8r2207_closed
theorem C8R02176_closed (row : List GridPoint) (h : FamilyMember row F8B001L4) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B001L4, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R02176G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02176G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02176G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02176G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02176G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02176G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02176G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02176G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R02176G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02176G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02176G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02176G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02176G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02176G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02176G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02176G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R02176G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02176G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02176G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02176G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02176G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02176G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02176G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02176G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R02176G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02176G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02176G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02176G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02176G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02176G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02176G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02176G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
