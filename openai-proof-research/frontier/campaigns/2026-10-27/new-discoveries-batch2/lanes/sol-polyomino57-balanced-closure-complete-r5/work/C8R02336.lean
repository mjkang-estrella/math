import F9All
import F8B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R02336G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2336_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] := by
    let c8r2336targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)]]
    let c8r2336choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,4),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2336targets [(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] c8r2336choice = true := by decide
    refine ⟨c8r2336targets, c8r2336choice, ?_, checked⟩
    intro S h
    simp only [c8r2336targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 26 _ (by rfl)
  have c8r2337_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] := by
    let c8r2337targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)]]
    let c8r2337choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,4),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2337targets [(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] c8r2337choice = true := by decide
    refine ⟨c8r2337targets, c8r2337choice, ?_, checked⟩
    intro S h
    simp only [c8r2337targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 28 _ (by rfl)
  have c8r2338_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] := by
    let c8r2338targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)]]
    let c8r2338choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,4),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2338targets [(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] c8r2338choice = true := by decide
    refine ⟨c8r2338targets, c8r2338choice, ?_, checked⟩
    intro S h
    simp only [c8r2338targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 30 _ (by rfl)
  have c8r2339_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] := by
    let c8r2339targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)]]
    let c8r2339choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,4),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2339targets [(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] c8r2339choice = true := by decide
    refine ⟨c8r2339targets, c8r2339choice, ?_, checked⟩
    intro S h
    simp only [c8r2339targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 3 _ (by rfl)
  have c8r2340_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r2340targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r2340choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,4),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2340targets [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] c8r2340choice = true := by decide
    refine ⟨c8r2340targets, c8r2340choice, ?_, checked⟩
    intro S h
    simp only [c8r2340targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 10 _ (by rfl)
  have c8r2341_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r2341targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r2341choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2341targets [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)] c8r2341choice = true := by decide
    refine ⟨c8r2341targets, c8r2341choice, ?_, checked⟩
    intro S h
    simp only [c8r2341targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 13 _ (by rfl)
  have c8r2342_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r2342targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r2342choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2342targets [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] c8r2342choice = true := by decide
    refine ⟨c8r2342targets, c8r2342choice, ?_, checked⟩
    intro S h
    simp only [c8r2342targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 15 _ (by rfl)
  have c8r2343_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c8r2343targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c8r2343choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2343targets [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] c8r2343choice = true := by decide
    refine ⟨c8r2343targets, c8r2343choice, ?_, checked⟩
    intro S h
    simp only [c8r2343targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 17 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2336_closed
  · subst row; exact c8r2337_closed
  · subst row; exact c8r2338_closed
  · subst row; exact c8r2339_closed
  · subst row; exact c8r2340_closed
  · subst row; exact c8r2341_closed
  · subst row; exact c8r2342_closed
  · subst row; exact c8r2343_closed
theorem C8R02336G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2344_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] := by
    let c8r2344targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c8r2344choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2344targets [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] c8r2344choice = true := by decide
    refine ⟨c8r2344targets, c8r2344choice, ?_, checked⟩
    intro S h
    simp only [c8r2344targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 20 _ (by rfl)
  have c8r2345_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] := by
    let c8r2345targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c8r2345choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2345targets [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] c8r2345choice = true := by decide
    refine ⟨c8r2345targets, c8r2345choice, ?_, checked⟩
    intro S h
    simp only [c8r2345targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 22 _ (by rfl)
  have c8r2346_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] := by
    let c8r2346targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c8r2346choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2346targets [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] c8r2346choice = true := by decide
    refine ⟨c8r2346targets, c8r2346choice, ?_, checked⟩
    intro S h
    simp only [c8r2346targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 25 _ (by rfl)
  have c8r2347_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] := by
    let c8r2347targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c8r2347choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2347targets [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] c8r2347choice = true := by decide
    refine ⟨c8r2347targets, c8r2347choice, ?_, checked⟩
    intro S h
    simp only [c8r2347targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 28 _ (by rfl)
  have c8r2348_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)] := by
    let c8r2348targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c8r2348choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2348targets [(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)] c8r2348choice = true := by decide
    refine ⟨c8r2348targets, c8r2348choice, ?_, checked⟩
    intro S h
    simp only [c8r2348targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 1 _ (by rfl)
  have c8r2349_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)] := by
    let c8r2349targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c8r2349choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2349targets [(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)] c8r2349choice = true := by decide
    refine ⟨c8r2349targets, c8r2349choice, ?_, checked⟩
    intro S h
    simp only [c8r2349targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 6 _ (by rfl)
  have c8r2350_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)] := by
    let c8r2350targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c8r2350choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2350targets [(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)] c8r2350choice = true := by decide
    refine ⟨c8r2350targets, c8r2350choice, ?_, checked⟩
    intro S h
    simp only [c8r2350targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 8 _ (by rfl)
  have c8r2351_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)] := by
    let c8r2351targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c8r2351choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2351targets [(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)] c8r2351choice = true := by decide
    refine ⟨c8r2351targets, c8r2351choice, ?_, checked⟩
    intro S h
    simp only [c8r2351targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2344_closed
  · subst row; exact c8r2345_closed
  · subst row; exact c8r2346_closed
  · subst row; exact c8r2347_closed
  · subst row; exact c8r2348_closed
  · subst row; exact c8r2349_closed
  · subst row; exact c8r2350_closed
  · subst row; exact c8r2351_closed
theorem C8R02336G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2352_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)] := by
    let c8r2352targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c8r2352choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2352targets [(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)] c8r2352choice = true := by decide
    refine ⟨c8r2352targets, c8r2352choice, ?_, checked⟩
    intro S h
    simp only [c8r2352targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 14 _ (by rfl)
  have c8r2353_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)] := by
    let c8r2353targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c8r2353choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2353targets [(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)] c8r2353choice = true := by decide
    refine ⟨c8r2353targets, c8r2353choice, ?_, checked⟩
    intro S h
    simp only [c8r2353targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 20 _ (by rfl)
  have c8r2354_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)] := by
    let c8r2354targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)]]
    let c8r2354choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2354targets [(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)] c8r2354choice = true := by decide
    refine ⟨c8r2354targets, c8r2354choice, ?_, checked⟩
    intro S h
    simp only [c8r2354targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 28 _ (by rfl)
  have c8r2355_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r2355targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r2355choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2355targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)] c8r2355choice = true := by decide
    refine ⟨c8r2355targets, c8r2355choice, ?_, checked⟩
    intro S h
    simp only [c8r2355targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 3 _ (by rfl)
  have c8r2356_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r2356targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r2356choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2356targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)] c8r2356choice = true := by decide
    refine ⟨c8r2356targets, c8r2356choice, ?_, checked⟩
    intro S h
    simp only [c8r2356targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 6 _ (by rfl)
  have c8r2357_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r2357targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r2357choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2357targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)] c8r2357choice = true := by decide
    refine ⟨c8r2357targets, c8r2357choice, ?_, checked⟩
    intro S h
    simp only [c8r2357targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 8 _ (by rfl)
  have c8r2358_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)] := by
    let c8r2358targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c8r2358choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2358targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)] c8r2358choice = true := by decide
    refine ⟨c8r2358targets, c8r2358choice, ?_, checked⟩
    intro S h
    simp only [c8r2358targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 10 _ (by rfl)
  have c8r2359_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)] := by
    let c8r2359targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c8r2359choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,1),(5,(0,0))),((2,4),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2359targets [(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)] c8r2359choice = true := by decide
    refine ⟨c8r2359targets, c8r2359choice, ?_, checked⟩
    intro S h
    simp only [c8r2359targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2352_closed
  · subst row; exact c8r2353_closed
  · subst row; exact c8r2354_closed
  · subst row; exact c8r2355_closed
  · subst row; exact c8r2356_closed
  · subst row; exact c8r2357_closed
  · subst row; exact c8r2358_closed
  · subst row; exact c8r2359_closed
theorem C8R02336G3 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2360_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)] := by
    let c8r2360targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c8r2360choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,1),(5,(0,0))),((2,4),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2360targets [(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)] c8r2360choice = true := by decide
    refine ⟨c8r2360targets, c8r2360choice, ?_, checked⟩
    intro S h
    simp only [c8r2360targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 21 _ (by rfl)
  have c8r2361_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c8r2361targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c8r2361choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,5),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2361targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)] c8r2361choice = true := by decide
    refine ⟨c8r2361targets, c8r2361choice, ?_, checked⟩
    intro S h
    simp only [c8r2361targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 31 _ (by rfl)
  have c8r2362_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c8r2362targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c8r2362choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,4),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2362targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)] c8r2362choice = true := by decide
    refine ⟨c8r2362targets, c8r2362choice, ?_, checked⟩
    intro S h
    simp only [c8r2362targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 3 _ (by rfl)
  have c8r2363_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c8r2363targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c8r2363choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2363targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)] c8r2363choice = true := by decide
    refine ⟨c8r2363targets, c8r2363choice, ?_, checked⟩
    intro S h
    simp only [c8r2363targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 6 _ (by rfl)
  have c8r2364_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c8r2364targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c8r2364choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2364targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)] c8r2364choice = true := by decide
    refine ⟨c8r2364targets, c8r2364choice, ?_, checked⟩
    intro S h
    simp only [c8r2364targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 8 _ (by rfl)
  have c8r2365_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c8r2365targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c8r2365choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2365targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)] c8r2365choice = true := by decide
    refine ⟨c8r2365targets, c8r2365choice, ?_, checked⟩
    intro S h
    simp only [c8r2365targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 10 _ (by rfl)
  have c8r2366_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)] := by
    let c8r2366targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c8r2366choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2366targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)] c8r2366choice = true := by decide
    refine ⟨c8r2366targets, c8r2366choice, ?_, checked⟩
    intro S h
    simp only [c8r2366targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 13 _ (by rfl)
  have c8r2367_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)] := by
    let c8r2367targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)]]
    let c8r2367choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,0),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2367targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)] c8r2367choice = true := by decide
    refine ⟨c8r2367targets, c8r2367choice, ?_, checked⟩
    intro S h
    simp only [c8r2367targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2360_closed
  · subst row; exact c8r2361_closed
  · subst row; exact c8r2362_closed
  · subst row; exact c8r2363_closed
  · subst row; exact c8r2364_closed
  · subst row; exact c8r2365_closed
  · subst row; exact c8r2366_closed
  · subst row; exact c8r2367_closed
theorem C8R02336_closed (row : List GridPoint) (h : FamilyMember row F8B001L9) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B001L9, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R02336G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02336G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02336G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02336G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02336G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02336G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02336G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02336G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R02336G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02336G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02336G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02336G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02336G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02336G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02336G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02336G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R02336G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02336G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02336G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02336G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02336G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02336G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02336G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02336G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R02336G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02336G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02336G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02336G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02336G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02336G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02336G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02336G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
